#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>  
#include <windows.h>

#define MATE 31000
#define INF 32000
#define MAX_PLY 128
#define U8 unsigned __int8
#define U16 unsigned __int16
#define S32 signed __int32
#define S64 signed __int64
#define U64 unsigned __int64
#define FALSE 0
#define TRUE 1
#define NAME "Frog"
#define VERSION "2025-12-30"
#define START_FEN "rnbqkbnr/pppppppp/8/8/8/8/PPPPPPPP/RNBQKBNR w KQkq - 0 1"

enum Color { WHITE, BLACK, COLOR_NB };
enum PieceType { PAWN, KNIGHT, BISHOP, ROOK, QUEEN, KING, PT_NB };
enum Bound { UPPER, LOWER, EXACT };

typedef struct {
	U64 castling[4];
	U64 color[2];
	U64 pieces[6];
	U64 ep;
	int flipped;
}Position;

Position pos;

typedef struct {
	int from;
	int to;
	int promo;
}Move;

typedef struct {
	int score;
	Move move;
	Move killer;
	Move moves_evaluated[256];
} Stack;

typedef struct {
	U64 key;
	Move move;
	int score;
	int depth;
	U16 flag;
}TT_Entry;

typedef struct {
	int post;
	int stop;
	int depthLimit;
	U64 timeStart;
	U64 timeLimit;
	U64 nodes;
	U64 nodesLimit;
}SSearchInfo;

SSearchInfo info;

U64 ranksBB[8] = {
	0x00000000000000ffULL,
	0x000000000000ff00ULL,
	0x0000000000ff0000ULL,
	0x00000000ff000000ULL,
	0x000000ff00000000ULL,
	0x0000ff0000000000ULL,
	0x00ff000000000000ULL,
	0xff00000000000000ULL };

U64 filesBB[8] = {
	0x0101010101010101ULL,
	0x0202020202020202ULL,
	0x0404040404040404ULL,
	0x0808080808080808ULL,
	0x1010101010101010ULL,
	0x2020202020202020ULL,
	0x4040404040404040ULL,
	0x8080808080808080ULL };

const U64 tt_count = 64ULL << 15;
int material[PT_NB] = { 100,320,330,500,900,0 };
Stack stack[128];
U64 keys[848];
int hash_count = 0;
U64 hash_history[1024] = { 0 };
S32 hh_table[2][2][64][64] = { 0 };
TT_Entry tt[64ULL << 15] = { 0 };

static U64 GetTimeMs() {
	return GetTickCount64();
}

static U64 FlipBitboard(const U64 bb) {
	return _byteswap_uint64(bb);
}

//least significant bit index
static U64 LSB(const U64 bb) {
	return _tzcnt_u64(bb);
}

static U64 Count(const U64 bb) {
	return _mm_popcnt_u64(bb);
}

static U64 East(const U64 bb) {
	return (bb << 1) & ~0x0101010101010101ULL;
}

static U64 West(const U64 bb) {
	return (bb >> 1) & ~0x8080808080808080ULL;
}

static U64 North(const U64 bb) {
	return bb << 8;
}

static U64 South(const U64 bb) {
	return bb >> 8;
}

static U64 NW(const U64 bb) {
	return North(West(bb));
}

static U64 NE(const U64 bb) {
	return North(East(bb));
}

static U64 SW(const U64 bb) {
	return South(West(bb));
}

static U64 SE(const U64 bb) {
	return South(East(bb));
}

static void Swap(U64* a, U64* b) {
	U64 temp = *a;
	*a = *b;
	*b = temp;
}

static int PieceTypeOn(Position* pos, int sq) {
	const U64 bb = 1ULL << sq;
	for (int i = PAWN; i < PT_NB; ++i)
		if (pos->pieces[i] & bb)
			return i;
	return PT_NB;
}

static U64 Ray(const U64 bb, const U64 blockers, U64(*f)(U64)) {
	U64 mask = f(bb);
	mask |= f(mask & ~blockers);
	mask |= f(mask & ~blockers);
	mask |= f(mask & ~blockers);
	mask |= f(mask & ~blockers);
	mask |= f(mask & ~blockers);
	mask |= f(mask & ~blockers);
	mask |= f(mask & ~blockers);
	return mask;
}

static U64 KnightAttackBB(const U64 bb) {
	return (((bb << 15) | (bb >> 17)) & 0x7F7F7F7F7F7F7F7FULL) | (((bb << 17) | (bb >> 15)) & 0xFEFEFEFEFEFEFEFEULL) |
		(((bb << 10) | (bb >> 6)) & 0xFCFCFCFCFCFCFCFCULL) | (((bb << 6) | (bb >> 10)) & 0x3F3F3F3F3F3F3F3FULL);
}

static U64 KnightAttack(const int sq) {
	return KnightAttackBB(1ULL << sq);
}

static U64 BishopAttackBB(U64 bb, U64 blockers) {
	return Ray(bb, blockers, NW) | Ray(bb, blockers, NE) | Ray(bb, blockers, SW) | Ray(bb, blockers, SE);
}

static U64 BishopAttack(const int sq, const U64 blockers) {
	return BishopAttackBB(1ULL << sq, blockers);
}

static U64 RookAttackBB(U64 bb, U64 blockers) {
	return Ray(bb, blockers, North) | Ray(bb, blockers, East) | Ray(bb, blockers, South) | Ray(bb, blockers, West);
}

static U64 RookAttack(const int sq, const U64 blockers) {
	return RookAttackBB(1ULL << sq, blockers);
}

static U64 KingAttackBB(const U64 bb) {
	return (bb << 8) | (bb >> 8) | (((bb >> 1) | (bb >> 9) | (bb << 7)) & 0x7F7F7F7F7F7F7F7FULL) |
		(((bb << 1) | (bb << 9) | (bb >> 7)) & 0xFEFEFEFEFEFEFEFEULL);
}

static U64 KingAttack(const int sq) {
	return KingAttackBB(1ULL << sq);
}

static void FlipPosition(Position* pos) {
	pos->color[0] = FlipBitboard(pos->color[0]);
	pos->color[1] = FlipBitboard(pos->color[1]);
	for (int i = PAWN; i < PT_NB; ++i)
		pos->pieces[i] = FlipBitboard(pos->pieces[i]);
	pos->ep = FlipBitboard(pos->ep);
	Swap(&pos->color[0], &pos->color[1]);
	Swap(&pos->castling[0], &pos->castling[2]);
	Swap(&pos->castling[1], &pos->castling[3]);
	pos->flipped = !pos->flipped;
}

static void PrintBitboard(U64 bb) {
	const char* s = "   +---+---+---+---+---+---+---+---+\n";
	const char* t = "     A   B   C   D   E   F   G   H\n";
	printf(t);
	for (int r = 7; r >= 0; r--) {
		printf(s);
		printf(" %d |", r + 1);
		for (int f = 0; f < 8; f++) {
			int sq = r * 8 + f;
			printf(" %c |", bb & 1ull << sq ? 'x' : ' ');
		}
		printf(" %d \n", r + 1);
	}
	printf(s);
	printf(t);
}

static void PrintBoard(Position* pos) {
	Position np = *pos;
	if (np.flipped)
		FlipPosition(&np);
	const char* s = "   +---+---+---+---+---+---+---+---+\n";
	const char* t = "     A   B   C   D   E   F   G   H\n";
	printf(t);
	for (int r = 7; r >= 0; r--) {
		printf(s);
		printf(" %d |", r + 1);
		for (int f = 0; f < 8; f++) {
			int sq = r * 8 + f;
			int piece = PieceTypeOn(&np, sq);
			if (np.color[0] & (1ull << sq))
				printf(" %c |", "ANBRQK "[piece]);
			else
				printf(" %c |", "anbrqk "[piece]);
		}
		printf(" %d \n", r + 1);
	}
	printf(s);
	printf(t);
	char castling[5] = "KQkq";
	for (int n = 0; n < 4; n++)
		if (!np.castling[n])
			castling[n] = '-';
	printf("side     : %10s\n", pos->flipped ? "black" : "white");
	printf("castling : %10s\n", castling);
}

int InputAvailable(void) {
	static int init = 0, pipe;
	static HANDLE inh;
	DWORD dw;

	if (!init) {
		init = 1;
		inh = GetStdHandle(STD_INPUT_HANDLE);
		pipe = !GetConsoleMode(inh, &dw);
		if (!pipe) {
			SetConsoleMode(inh, dw & ~(ENABLE_MOUSE_INPUT | ENABLE_WINDOW_INPUT));
			FlushConsoleInputBuffer(inh);
		}
	}
	if (pipe) {
		if (!PeekNamedPipe(inh, NULL, 0, NULL, &dw, NULL))
			return 1;
		return dw > 0;
	}
	else {
		GetNumberOfConsoleInputEvents(inh, &dw);
		return dw > 1;
	}
}

static void CheckUp() {
	if ((info.timeLimit && GetTimeMs() - info.timeStart > info.timeLimit) || (info.nodesLimit && info.nodes > info.nodesLimit))
		info.stop = 1;
	if (InputAvailable()) {
		char line[4000];
		fgets(line, sizeof(line), stdin);
		if (!strncmp(line, "stop", 4))
			info.stop = 1;
	}
}

static U64 Attacked(Position* pos, int sq, int them) {
	const U64 bb = 1ULL << sq;
	const U64 kt = pos->color[them] & pos->pieces[KNIGHT];
	const U64 BQ = pos->pieces[BISHOP] | pos->pieces[QUEEN];
	const U64 RQ = pos->pieces[ROOK] | pos->pieces[QUEEN];
	const U64 pawns = pos->color[them] & pos->pieces[PAWN];
	const U64 pawn_attacks = them ? SW(pawns) | SE(pawns) : NW(pawns) | NE(pawns);
	return (pawn_attacks & bb) | (kt & KnightAttack(sq)) |
		(BishopAttack(sq, pos->color[0] | pos->color[1]) & pos->color[them] & BQ) |
		(RookAttack(sq, pos->color[0] | pos->color[1]) & pos->color[them] & RQ) |
		(KingAttack(sq) & pos->color[them] & pos->pieces[KING]);
}

static void add_move(Move* const movelist, int* num_moves, const int from, const int to, const int promo) {
	Move* m = &movelist[(*num_moves)++];
	m->from = from;
	m->to = to;
	m->promo = promo;
}

static void generate_pawn_moves(Move* const movelist, int* num_moves, U64 to_mask, const int offset) {
	while (to_mask) {
		const int to = (int)LSB(to_mask);
		to_mask &= to_mask - 1;
		if (to >= 56) {
			add_move(movelist, num_moves, to + offset, to, QUEEN);
			add_move(movelist, num_moves, to + offset, to, ROOK);
			add_move(movelist, num_moves, to + offset, to, BISHOP);
			add_move(movelist, num_moves, to + offset, to, KNIGHT);
		}
		else
			add_move(movelist, num_moves, to + offset, to, PT_NB);
	}
}

static void generate_piece_moves(Move* const movelist, int* num_moves, const Position* pos, const int piece, const U64 to_mask, U64(*func)(int, U64)) {
	U64 copy = pos->color[0] & pos->pieces[piece];
	while (copy) {
		const int fr = LSB(copy);
		copy &= copy - 1;
		U64 moves = func(fr, pos->color[0] | pos->color[1]) & to_mask;
		while (moves) {
			const int to = LSB(moves);
			moves &= moves - 1;
			add_move(movelist, num_moves, fr, to, PT_NB);
		}
	}
}

static int MoveGen(const Position* pos, Move* const movelist, int only_captures) {
	int num_moves = 0;
	const U64 all = pos->color[0] | pos->color[1];
	const U64 to_mask = only_captures ? pos->color[1] : ~pos->color[0];
	const U64 pawns = pos->color[0] & pos->pieces[PAWN];
	U64 maskTo = North(pawns) & ~all & (only_captures ? 0xFF00000000000000ULL : 0xFFFFFFFFFFFF0000ULL);
	generate_pawn_moves(movelist, &num_moves, maskTo, -8);
	if (!only_captures) {
		generate_pawn_moves(movelist, &num_moves, North(North(pawns & 0xFF00ULL) & ~all) & ~all, -16);
	}
	generate_pawn_moves(movelist, &num_moves, NW(pawns) & (pos->color[1] | pos->ep), -7);
	generate_pawn_moves(movelist, &num_moves, NE(pawns) & (pos->color[1] | pos->ep), -9);
	generate_piece_moves(movelist, &num_moves, pos, KNIGHT, to_mask, KnightAttack);
	generate_piece_moves(movelist, &num_moves, pos, BISHOP, to_mask, BishopAttack);
	generate_piece_moves(movelist, &num_moves, pos, QUEEN, to_mask, BishopAttack);
	generate_piece_moves(movelist, &num_moves, pos, ROOK, to_mask, RookAttack);
	generate_piece_moves(movelist, &num_moves, pos, QUEEN, to_mask, RookAttack);
	generate_piece_moves(movelist, &num_moves, pos, KING, to_mask, KingAttack);
	if (!only_captures && pos->castling[0] && !(all & 0x60ULL) && !Attacked(pos, 4, 1) && !Attacked(pos, 5, 1)) {
		add_move(movelist, &num_moves, 4, 6, PT_NB);
	}
	if (!only_captures && pos->castling[1] && !(all & 0xEULL) && !Attacked(pos, 4, 1) && !Attacked(pos, 3, 1)) {
		add_move(movelist, &num_moves, 4, 2, PT_NB);
	}
	return num_moves;
}

static int IsRepetition(U64 hash) {
	for (int n = hash_count - 4; n >= 0; n -= 2)
		if (hash_history[n] == hash)
			return 1;
	return 0;
}

static U64 Rand64() {
	static U64 next = 1;
	next = next * 12345104729 + 104723;
	return next;
}

void InitHashKeys() {
	for (int i = 0; i < 848; ++i)
		keys[i] = Rand64();
}

static U64 GetHash(const Position* pos) {
	U64 hash = pos->flipped;
	for (S32 p = PAWN; p < PT_NB; ++p) {
		U64 copy = pos->pieces[p] & pos->color[0];
		while (copy) {
			const S32 sq = LSB(copy);
			copy &= copy - 1;
			hash ^= keys[p * 64 + sq];
		}
		copy = pos->pieces[p] & pos->color[1];
		while (copy) {
			const S32 sq = LSB(copy);
			copy &= copy - 1;
			hash ^= keys[p * 64 + sq + 6 * 64];
		}
	}
	if (pos->ep)
		hash ^= keys[12 * 64 + LSB(pos->ep)];
	hash ^= keys[13 * 64 + pos->castling[0] + pos->castling[1] * 2 + pos->castling[2] * 4 + pos->castling[3] * 8];
	return hash;
}

static void SetFen(Position* pos, char* fen) {
	memset(pos, 0, sizeof(Position));
	int i = 0;
	int z = 0;
	int sq = 56;
	int n = (int)strlen(fen);
	for (i = 0; i < n && !z; ++i) {
		U64 bb = 1ull << sq;
		switch (fen[i]) {
		case '1': sq += 1; break;
		case '2': sq += 2; break;
		case '3': sq += 3; break;
		case '4': sq += 4; break;
		case '5': sq += 5; break;
		case '6': sq += 6; break;
		case '7': sq += 7; break;
		case '8': sq += 8; break;
		case 'P': pos->color[0] |= bb; pos->pieces[PAWN] |= bb; ++sq; break;
		case 'N': pos->color[0] |= bb; pos->pieces[KNIGHT] |= bb; ++sq; break;
		case 'B': pos->color[0] |= bb; pos->pieces[BISHOP] |= bb; ++sq; break;
		case 'R': pos->color[0] |= bb; pos->pieces[ROOK] |= bb; ++sq; break;
		case 'Q': pos->color[0] |= bb; pos->pieces[QUEEN] |= bb; ++sq; break;
		case 'K': pos->color[0] |= bb; pos->pieces[KING] |= bb; ++sq; break;
		case 'p': pos->color[1] |= bb; pos->pieces[PAWN] |= bb; ++sq; break;
		case 'n': pos->color[1] |= bb; pos->pieces[KNIGHT] |= bb; ++sq; break;
		case 'b': pos->color[1] |= bb; pos->pieces[BISHOP] |= bb; ++sq; break;
		case 'r': pos->color[1] |= bb; pos->pieces[ROOK] |= bb; ++sq; break;
		case 'q': pos->color[1] |= bb; pos->pieces[QUEEN] |= bb; ++sq; break;
		case 'k': pos->color[1] |= bb; pos->pieces[KING] |= bb; ++sq; break;
		case '/': sq -= 16; break;
		default: z = 1; break;
		}
	}
	int flipped = fen[i++] == 'w' ? 0 : 1;
	i++;
	for (z = 0; i < n && !z; ++i) {
		switch (fen[i]) {
		case 'K': pos->castling[0] = 1; break;
		case 'Q': pos->castling[1] = 1; break;
		case 'k': pos->castling[2] = 1; break;
		case 'q': pos->castling[3] = 1; break;
		case '-': break;
		default: z = 1; break;
		}
	}
	if (fen[i] != '-') {
		const int sq = fen[i] - 'a' + 8 * (fen[++i] - '1');
		pos->ep = 1ull << sq;
	}
	if (flipped)FlipPosition(pos);
}

static char* ParseToken(char* string, char* token) {
	while (*string == ' ')
		string++;
	while (*string != ' ' && *string != '\0')
		*token++ = *string++;
	*token = '\0';
	return string;
}

static int MakeMove(Position* pos, const Move* move) {
	const int piece = PieceTypeOn(pos, move->from);
	const int captured = PieceTypeOn(pos, move->to);
	const U64 to = 1ULL << move->to;
	const U64 from = 1ULL << move->from;
	pos->color[0] ^= from | to;
	pos->pieces[piece] ^= from | to;
	if (piece == PAWN && to == pos->ep) {
		pos->color[1] ^= to >> 8;
		pos->pieces[PAWN] ^= to >> 8;
	}
	pos->ep = 0x0ULL;
	if (piece == PAWN && move->to - move->from == 16) {
		pos->ep = to >> 8;
	}
	if (captured != PT_NB) {
		pos->color[1] ^= to;
		pos->pieces[captured] ^= to;
	}
	if (piece == KING) {
		const U64 bb = move->to - move->from == 2 ? 0xa0ULL : move->to - move->from == -2 ? 0x9ULL : 0x0ULL;
		pos->color[0] ^= bb;
		pos->pieces[ROOK] ^= bb;
	}
	if (piece == PAWN && move->to >= 56) {
		pos->pieces[PAWN] ^= to;
		pos->pieces[move->promo] ^= to;
	}
	pos->castling[0] &= !((from | to) & 0x90ULL);
	pos->castling[1] &= !((from | to) & 0x11ULL);
	pos->castling[2] &= !((from | to) & 0x9000000000000000ULL);
	pos->castling[3] &= !((from | to) & 0x1100000000000000ULL);
	FlipPosition(pos);
	return !Attacked(pos, LSB(pos->color[1] & pos->pieces[KING]), 0);
}

static char* MoveToUci(Move move, int flip) {
	static char str[6] = { 0 };
	str[0] = 'a' + (move.from % 8);
	str[1] = '1' + (flip ? (7 - move.from / 8) : (move.from / 8));
	str[2] = 'a' + (move.to % 8);
	str[3] = '1' + (flip ? (7 - move.to / 8) : (move.to / 8));
	str[4] = "\0nbrq\0\0"[move.promo];
	return str;
}

static Move UciToMove(char* s, int flip) {
	Move m;
	m.from = (s[0] - 'a');
	int f = (s[1] - '1');
	m.from += 8 * (flip ? 7 - f : f);
	m.to = (s[2] - 'a');
	f = (s[3] - '1');
	m.to += 8 * (flip ? 7 - f : f);
	m.promo = PT_NB;
	switch (s[4]) {
	case 'N':
	case 'n':
		m.promo = KNIGHT;
		break;
	case 'B':
	case 'b':
		m.promo = BISHOP;
		break;
	case 'R':
	case 'r':
		m.promo = ROOK;
		break;
	case 'Q':
	case 'q':
		m.promo = QUEEN;
		break;
	}
	return m;
}

static int EvalPosition(Position* pos) {
	int score = 0;
	U64 bbBlockers = pos->color[0] | pos->color[1];
	for (int c = WHITE; c < COLOR_NB; c++) {
		for (int pt = PAWN; pt < KING; ++pt)
			score += material[pt] * Count(pos->color[0] & pos->pieces[pt]);
		U64 bbStart1 = pos->color[1] & pos->pieces[PAWN];
		U64 bbControl1 = SW(bbStart1) | SE(bbStart1);
		score -= Count(bbControl1);
		U64 bbStart0 = pos->color[0] & pos->pieces[KNIGHT];
		U64 bbAttack0 = KnightAttackBB(bbStart0) & ~bbControl1;
		score += Count(bbAttack0);
		bbStart0 = pos->color[0] & (pos->pieces[BISHOP] | pos->pieces[QUEEN]);
		bbAttack0 = BishopAttackBB(bbStart0, bbBlockers) & ~bbControl1;
		score += Count(bbAttack0);
		bbStart0 = pos->color[0] & (pos->pieces[ROOK] | pos->pieces[QUEEN]);
		bbAttack0 = RookAttackBB(bbStart0, bbBlockers) & ~bbControl1;
		score += Count(bbAttack0);
		bbStart0 = pos->color[0] & pos->pieces[KING];
		U64 file0 = filesBB[LSB(bbStart0) % 8];
		file0 |= East(file0) | West(file0);
		bbAttack0 = file0 & (ranksBB[1] | ranksBB[2]) & ~(filesBB[3] | filesBB[4]);
		bbAttack0 &= (pos->color[0] & pos->pieces[PAWN]);
		score += Count(bbAttack0);
		score += Count(bbAttack0 & ranksBB[1]);
		FlipPosition(pos);
		score = -score;
	}
	return score;
}

static int Equal(const Move lhs, const Move rhs) {
	return !memcmp(&rhs, &lhs, sizeof(Move));
}

static int IsPseudolegalMove(const Position* pos, const Move move) {
	Move moves[256];
	const int num_moves = MoveGen(pos, moves, 0);
	for (int i = 0; i < num_moves; ++i)
		if (moves[i].from == move.from && moves[i].to == move.to)
			return 1;
	return 0;
}

static void PrintPv(const Position* pos, const Move move) {
	if (!IsPseudolegalMove(pos, move))
		return;
	const Position npos = *pos;
	if (!MakeMove(&npos, &move))
		return;
	printf(" %s", MoveToUci(move, pos->flipped));
	const U64 tt_key = GetHash(&npos);
	TT_Entry* tt_entry = tt + (tt_key % tt_count);
	if (tt_entry->key != tt_key || (!tt_entry->move.from && !tt_entry->move.to) || tt_entry->flag != EXACT)
		return;
	if (IsRepetition(tt_key))
		return;
	hash_history[hash_count++] = tt_key;
	PrintPv(&npos, tt_entry->move);
	hash_count--;
}

static int Permill() {
	int pm = 0;
	for (int n = 0; n < 1000; n++) {
		if (tt[n].key)
			pm++;
	}
	return pm;
}

static int SearchAlpha(Position* pos, int alpha, int beta, int depth, int ply, Stack* stack) {
	if (!(++info.nodes & 0xffff))
		CheckUp();
	if (info.stop)
		return 0;
	const int static_eval = EvalPosition(pos);
	if (ply >= MAX_PLY)
		return static_eval;
	stack[ply].score = static_eval;
	const U64 in_check = Attacked(pos, (int)LSB(pos->color[0] & pos->pieces[KING]), 1);
	if (in_check)
		depth = max(1, depth + 1);
	int in_qsearch = depth <= 0;
	const U64 tt_key = GetHash(pos);
	if (ply > 0 && !in_qsearch)
		if (IsRepetition(tt_key))
			return 0;
	// TT Probing
	TT_Entry* tt_entry = tt + (tt_key % tt_count);
	Move tt_move = { 0 };
	if (tt_entry->key == tt_key) {
		tt_move = tt_entry->move;
		if (alpha == beta - 1 && tt_entry->depth >= depth) {
			if (tt_entry->flag == EXACT)
				return tt_entry->score;
			if (tt_entry->flag == LOWER && tt_entry->score <= alpha)
				return tt_entry->score;
			if (tt_entry->flag == UPPER && tt_entry->score >= beta)
				return tt_entry->score;
		}
	}
	else
		depth -= depth > 3;
	const S32 improving = ply > 1 && static_eval > stack[ply - 2].score;
	if (in_qsearch && static_eval > alpha) {
		if (static_eval >= beta)
			return beta;
		alpha = static_eval;
	}
	S32 num_moves_evaluated = 0;
	U8 tt_flag = LOWER;
	Move best_move = { 0 };
	int best_score = -INF;
	Move moves[256];
	hash_history[hash_count++] = tt_key;
	const int num_moves = MoveGen(pos, moves, in_qsearch);
	S64 move_scores[256];
	for (int j = 0; j < num_moves; ++j) {
		const int capture = PieceTypeOn(pos, moves[j].to);
		if (Equal(moves[j], tt_move))
			move_scores[j] = 1LL << 62;
		else if (capture != PT_NB)
			move_scores[j] = ((capture + 1) * (1LL << 54)) - PieceTypeOn(pos, moves[j].from);
		else if (Equal(moves[j], stack[ply].killer))
			move_scores[j] = 1LL << 50;
		else
			move_scores[j] = hh_table[pos->flipped][moves[j].from][moves[j].to];
	}
	for (int i = 0; i < num_moves; ++i) {
		int bstIdx = i;
		S64 bstVal = move_scores[i];
		for (int j = i + 1; j < num_moves; ++j) {
			if (move_scores[j] > bstVal) {
				bstIdx = j;
				bstVal = move_scores[j];
			}
		}
		Move move = moves[bstIdx];
		const S32 gain = material[move.promo] + material[PieceTypeOn(pos, move.to)];
		move_scores[bstIdx] = move_scores[i];
		moves[bstIdx] = moves[i];
		Position npos = *pos;
		if (!MakeMove(&npos, &move))
			continue;
		S32 score;
		S32 reduction = depth > 3 && num_moves_evaluated > 1
			? max(num_moves_evaluated / 13 + depth / 14 + (alpha == beta - 1) + !improving -
				min(max(hh_table[pos->flipped][!gain][move.from][move.to] / 128, -2), 2),
				0)
			: 0;

		while (num_moves_evaluated &&
			(score = -SearchAlpha(&npos,
				-alpha - 1,
				-alpha,
				depth - reduction - 1,
				ply + 1,
				stack)) > alpha &&
			reduction > 0)
			reduction = 0;

		if (!num_moves_evaluated || score > alpha && score < beta)
			score = -SearchAlpha(&npos,
				-beta,
				-alpha,
				depth - 1,
				ply + 1,
				stack);
		if (info.stop) {
			hash_count--;
			return 0;
		}
		if (score > best_score) {
			best_score = score;
			best_move = move;
			if (score > alpha) {
				alpha = score;
				tt_flag = EXACT;
				stack[ply].move = move;
				if (!ply && info.post)
				{
					printf("info depth %d score ", depth);
					if (abs(score) < MATE - MAX_PLY)
						printf("cp %d", score);
					else
						printf("mate %d", (score > 0 ? (MATE - score + 1) >> 1 : -(MATE + score) >> 1));
					printf(" time %lld", GetTimeMs() - info.timeStart);
					printf(" nodes %lld", info.nodes);
					printf(" hashfull %d pv",Permill());
					PrintPv(pos, stack[0].move);
					printf("\n");
				}
			}
		}
		if (alpha >= beta) {
			tt_flag = UPPER;
			if (!gain)
				stack[ply].killer = move;
			hh_table[pos->flipped][!gain][move.from][move.to] +=
				depth * depth - depth * depth * hh_table[pos->flipped][!gain][move.from][move.to] / 512;
			for (S32 j = 0; j < num_moves_evaluated; ++j) {
				const S32 prev_gain = material[stack[ply].moves_evaluated[j].promo] + material[PieceTypeOn(pos, stack[ply].moves_evaluated[j].to)];
				hh_table[pos->flipped][!prev_gain][stack[ply].moves_evaluated[j].from][stack[ply].moves_evaluated[j].to] -=
					depth * depth +
					depth * depth *
					hh_table[pos->flipped][!prev_gain][stack[ply].moves_evaluated[j].from][stack[ply].moves_evaluated[j].to] / 512;
			}
			break;
		}
		stack[ply].moves_evaluated[num_moves_evaluated++] = move;
	}
	hash_count--;
	if (best_score == -INF)
		return in_qsearch ? alpha : in_check ? ply - MATE : 0;
	else {
		tt_entry->key = tt_key;
		tt_entry->move = best_move;
		tt_entry->depth = depth;
		tt_entry->score = best_score;
		tt_entry->flag = tt_flag;
	}
	return alpha;
}

static void SearchIteratively(Position* pos) {
	for (int depth = 1; depth <= info.depthLimit; ++depth) {
		SearchAlpha(pos, -MATE, MATE, depth, 0, stack);
		if (info.stop)
			break;
		if (info.timeLimit && GetTimeMs() - info.timeStart > info.timeLimit / 2) {
			break;
		}
	}
	if (info.post) {
		char* uci = MoveToUci(stack[0].move, pos->flipped);
		printf("bestmove %s\n", uci);
		fflush(stdout);
	}
}

static inline void PerftDriver(Position* pos, int depth) {
	Move moves[256];
	const int num_moves = MoveGen(pos, moves, 0);
	for (int n = 0; n < num_moves; n++){
		Position npos = *pos;
		if (!MakeMove(&npos, &moves[n]))
			continue;
		if (depth)
			PerftDriver(&npos, depth - 1);
		else
			info.nodes++;
	}
}

static int ShrinkNumber(U64 n) {
	if (n < 10000)
		return 0;
	if (n < 10000000)
		return 1;
	if (n < 10000000000)
		return 2;
	return 3;
}

static void PrintSummary(U64 time, U64 nodes) {
	U64 nps = (nodes * 1000) / max(time, 1);
	const char* units[] = { "", "k", "m", "g" };
	int sn = ShrinkNumber(nps);
	int p = pow(10, sn * 3);
	int b = pow(10, 3);
	printf("-----------------------------\n");
	printf("Time        : %llu\n", time);
	printf("Nodes       : %llu\n", nodes);
	printf("Nps         : %llu (%llu%s/s)\n", nps, nps / p, units[sn]);
	printf("-----------------------------\n");
}

void ResetInfo() {
	info.timeStart = GetTimeMs();
	info.timeLimit = 0;
	info.depthLimit = MAX_PLY;
	info.nodesLimit = 0;
	info.nodes = 0;
	info.stop = FALSE;
	info.post = TRUE;
}

void PrintPerformanceHeader() {
	printf("-----------------------------\n");
	printf("ply      time        nodes\n");
	printf("-----------------------------\n");
}

//performance test
static inline void UciPerformance() {
	ResetInfo();
	PrintPerformanceHeader();
	SetFen(&pos, START_FEN);
	info.depthLimit = 0;
	U64 elapsed = 0;
	while (elapsed < 3000) {
		PerftDriver(&pos, info.depthLimit++);
		elapsed = GetTimeMs() - info.timeStart;
		printf(" %2llu. %8llu %12llu\n", info.depthLimit, elapsed, info.nodes);
	}
	PrintSummary(elapsed, info.nodes);
}

//start benchmark
static void UciBench() {
	ResetInfo();
	PrintPerformanceHeader();
	SetFen(&pos, START_FEN);
	info.depthLimit = 0;
	info.post = FALSE;
	U64 elapsed = 0;
	while (elapsed < 3000)
	{
		++info.depthLimit;
		SearchIteratively(&pos);
		elapsed = GetTimeMs() - info.timeStart;
		printf(" %2d. %8llu %12llu\n", info.depthLimit, elapsed, info.nodes);
	}
	PrintSummary(elapsed, info.nodes);
}

static void ParsePosition(char* ptr) {
	char token[80], fen[80];
	ptr = ParseToken(ptr, token);
	if (strcmp(token, "fen") == 0) {
		fen[0] = '\0';
		while (1) {
			ptr = ParseToken(ptr, token);
			if (*token == '\0' || strcmp(token, "moves") == 0)
				break;
			strcat(fen, token);
			strcat(fen, " ");
		}
		SetFen(&pos, fen);
	}
	else {
		ptr = ParseToken(ptr, token);
		SetFen(&pos, START_FEN);
	}
	hash_count = 0;
	if (strcmp(token, "moves") == 0)
		while (1) {
			hash_history[hash_count++] = GetHash(&pos);
			ptr = ParseToken(ptr, token);
			if (*token == '\0')
				break;
			Move m = UciToMove(token, pos.flipped);
			if (!MakeMove(&pos, &m))
				printf("Illegal move (%s).\n", token);
		}
}

static void ParseGo(char* command) {
	ResetInfo();
	int wtime = 0;
	int btime = 0;
	int winc = 0;
	int binc = 0;
	int movestogo = 32;
	char* argument = NULL;
	if (argument = strstr(command, "binc"))
		binc = atoi(argument + 5);
	if (argument = strstr(command, "winc"))
		winc = atoi(argument + 5);
	if (argument = strstr(command, "wtime"))
		wtime = atoi(argument + 6);
	if (argument = strstr(command, "btime"))
		btime = atoi(argument + 6);
	if ((argument = strstr(command, "movestogo")))
		movestogo = atoi(argument + 10);
	if ((argument = strstr(command, "movetime")))
		info.timeLimit = atoi(argument + 9);
	if ((argument = strstr(command, "depth")))
		info.depthLimit = atoi(argument + 6);
	if (argument = strstr(command, "nodes"))
		info.nodesLimit = atoi(argument + 5);
	int time = pos.flipped ? btime : wtime;
	int inc = pos.flipped ? binc : winc;
	if (time)
		info.timeLimit = min(time / movestogo + inc, time / 2);
	SearchIteratively(&pos);
}

static void UciCommand(char* line) {
	if (!strncmp(line, "isready", 7)) {
		printf("readyok\n");
		fflush(stdout);
	}
	else if (!strncmp(line, "ucinewgame", 10))
		memset(hh_table, 0, sizeof(hh_table));
	else if (!strncmp(line, "uci", 3)) {
		printf("id name %s\nuciok\n", NAME);
		fflush(stdout);
	}
	else if (!strncmp(line, "go", 2))
		ParseGo(line + 2);
	else if (!strncmp(line, "position", 8))
		ParsePosition(line + 8);
	else if (!strncmp(line, "print", 5))
		PrintBoard(&pos);
	else if (!strncmp(line, "perft", 5))
		UciPerformance();
	else if (!strncmp(line, "bench", 5))
		UciBench();
	else if (!strncmp(line, "exit", 4))
		exit(0);
}

static void UciLoop() {
	char line[4000];
	while (fgets(line, sizeof(line), stdin))
		UciCommand(line);
}

int main(const int argc, const char** argv) {
	printf("%s %s\n", NAME, VERSION);
	InitHashKeys();
	SetFen(&pos, START_FEN);
	UciLoop();
}
