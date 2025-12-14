#include <iostream>
#include <sstream> 
#include <random>

#define MAX_DEPTH 100
#define MATE 30000
#define INF 32000
#define U8 unsigned __int8
#define S16 signed __int16
#define U16 unsigned __int16
#define S32 signed __int32
#define S64 signed __int64
#define U64 unsigned __int64
#define NAME "Frog"
#define VERSION "2025-12-12"
#define START_FEN "rnbqkbnr/pppppppp/8/8/8/8/PPPPPPPP/RNBQKBNR w KQkq - 0 1"

using namespace std;

enum Color { WHITE, BLACK, COLOR_NB };
enum PieceType { PAWN, KNIGHT, BISHOP, ROOK, QUEEN, KING, PT_NB };
enum Bound { LOWER, EXACT,  UPPER };

struct Position {
	int castling[4]{};
	U64 color[2]{};
	U64 pieces[6]{};
	U64 ep = 0x0ULL;
	bool flipped = false;
}pos;

struct Move {
	U8 from = 0;
	U8 to = 0;
	U8 promo = 0;
};

const Move no_move{};

struct Stack {
	Move moves[256];
	Move moves_evaluated[256];
	S64 moves_scores[256];
	Move move;
	Move killer;
};

struct TT_Entry {
	U64 key;
	Move move;
	U8 flag;
	S16 score;
	S16 depth;
};

struct SSearchInfo {
	bool stop = false;
	int depthLimit = MAX_DEPTH;
	S64 timeStart = 0;
	S64 timeLimit = 0;
	U64 nodes = 0;
	U64 nodesLimit = 0;
}info;

constexpr U64 FileABB = 0x0101010101010101ULL;
constexpr U64 FileBBB = FileABB << 1;
constexpr U64 FileCBB = FileABB << 2;
constexpr U64 FileDBB = FileABB << 3;
constexpr U64 FileEBB = FileABB << 4;
constexpr U64 FileFBB = FileABB << 5;
constexpr U64 FileGBB = FileABB << 6;
constexpr U64 FileHBB = FileABB << 7;

constexpr U64 Rank1BB = 0xFF;
constexpr U64 Rank2BB = Rank1BB << (8 * 1);
constexpr U64 Rank3BB = Rank1BB << (8 * 2);
constexpr U64 Rank4BB = Rank1BB << (8 * 3);
constexpr U64 Rank5BB = Rank1BB << (8 * 4);
constexpr U64 Rank6BB = Rank1BB << (8 * 5);
constexpr U64 Rank7BB = Rank1BB << (8 * 6);
constexpr U64 Rank8BB = Rank1BB << (8 * 7);

U64 filesBB[8] = { FileABB,FileBBB,FileCBB,FileDBB,FileEBB,FileFBB,FileGBB,FileHBB };

const U64 num_tt_entries = 64ULL << 15;  // The first value is the size in megabytes
int material[PT_NB] = { 100,320,330,500,900,0 };
U64 keys[848];
Stack stack[128]{};
S64 hh_table[2][64][64]{};
TT_Entry transposition_table[num_tt_entries] = {};
int hash_count = 0;
U64 hash_history[1024]{};

static bool IsRepetition(const Position& pos, U64 hash) {
	for (int n = hash_count - 2; n >= 0; n -= 2)
		if (hash_history[n] == hash)
			return true;
	return false;
}

static S64 GetTimeMs() {
	return (clock() * 1000) / CLOCKS_PER_SEC;
}

static U64 Flip(const U64 bb) {
	return _byteswap_uint64(bb);
}

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

static U64 NN(const U64 bb) {
	return bb << 16;
}

static U64 SS(const U64 bb) {
	return bb >> 16;
}

static void FlipPosition(Position& pos) {
	pos.color[0] = Flip(pos.color[0]);
	pos.color[1] = Flip(pos.color[1]);
	for (int i = 0; i < 6; ++i) {
		pos.pieces[i] = Flip(pos.pieces[i]);
	}
	pos.ep = Flip(pos.ep);
	swap(pos.color[0], pos.color[1]);
	swap(pos.castling[0], pos.castling[2]);
	swap(pos.castling[1], pos.castling[3]);
	pos.flipped = !pos.flipped;
}

auto operator==(const Move& lhs, const Move& rhs) {
	return !memcmp(&rhs, &lhs, sizeof(Move));
}

static string MoveToUci(const Move& move, const int flip) {
	string str;
	str += 'a' + (move.from % 8);
	str += '1' + (flip ? (7 - move.from / 8) : (move.from / 8));
	str += 'a' + (move.to % 8);
	str += '1' + (flip ? (7 - move.to / 8) : (move.to / 8));
	if (move.promo != PT_NB)
		str += "\0nbrq\0\0"[move.promo];
	return str;
}

static Move UciToMove(string& uci, int flip) {
	Move m;
	m.from = (uci[0] - 'a');
	int f = (uci[1] - '1');
	m.from += 8 * (flip ? 7 - f : f);
	m.to = (uci[2] - 'a');
	f = (uci[3] - '1');
	m.to += 8 * (flip ? 7 - f : f);
	m.promo = PT_NB;
	switch (uci[4]) {
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

static int PieceTypeOn(const Position& pos, const int sq) {
	const U64 bb = 1ULL << sq;
	for (int i = 0; i < 6; ++i) {
		if (pos.pieces[i] & bb) {
			return i;
		}
	}
	return PT_NB;
}

template <typename F>
U64 Ray(const U64 bb, const U64 blockers, F f) {
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

static U64 BbKnightAttack(const U64 bb) {
	return (((bb << 15) | (bb >> 17)) & 0x7F7F7F7F7F7F7F7FULL) | (((bb << 17) | (bb >> 15)) & 0xFEFEFEFEFEFEFEFEULL) |
		(((bb << 10) | (bb >> 6)) & 0xFCFCFCFCFCFCFCFCULL) | (((bb << 6) | (bb >> 10)) & 0x3F3F3F3F3F3F3F3FULL);
}

static U64 KnightAttack(const int sq, const U64) {
	return BbKnightAttack(1ULL << sq);
}

static U64 BbBishopAttack(const U64 bb, const U64 blockers) {
	return Ray(bb, blockers, NW) | Ray(bb, blockers, NE) | Ray(bb, blockers, SW) | Ray(bb, blockers, SE);
}

static U64 BishopAttack(const int sq, const U64 blockers) {
	return BbBishopAttack(1ULL << sq, blockers);
}

static U64 BbRookAttack(const U64 bb, const U64 blockers) {
	return Ray(bb, blockers, North) | Ray(bb, blockers, East) | Ray(bb, blockers, South) | Ray(bb, blockers, West);
}

static U64 RookAttack(const int sq, const U64 blockers) {
	return BbRookAttack(1ULL << sq, blockers);
}

static U64 KingAttack(const int sq, const U64) {
	const U64 bb = 1ULL << sq;
	return (bb << 8) | (bb >> 8) |
		(((bb >> 1) | (bb >> 9) | (bb << 7)) & 0x7F7F7F7F7F7F7F7FULL) |
		(((bb << 1) | (bb << 9) | (bb >> 7)) & 0xFEFEFEFEFEFEFEFEULL);
}

static bool Attacked(const Position& pos, const int sq, const int them = true) {
	const U64 bb = 1ULL << sq;
	const U64 kt = pos.color[them] & pos.pieces[KNIGHT];
	const U64 BQ = pos.pieces[BISHOP] | pos.pieces[QUEEN];
	const U64 RQ = pos.pieces[ROOK] | pos.pieces[QUEEN];
	const U64 pawns = pos.color[them] & pos.pieces[PAWN];
	const U64 pawn_attacks = them ? SW(pawns) | SE(pawns) : NW(pawns) | NE(pawns);
	return (pawn_attacks & bb) | (kt & KnightAttack(sq, 0)) |
		(BishopAttack(sq, pos.color[0] | pos.color[1]) & pos.color[them] & BQ) |
		(RookAttack(sq, pos.color[0] | pos.color[1]) & pos.color[them] & RQ) |
		(KingAttack(sq, 0) & pos.color[them] & pos.pieces[KING]);
}

static auto MakeMove(Position& pos, const Move& move) {
	const int piece = PieceTypeOn(pos, move.from);
	const int captured = PieceTypeOn(pos, move.to);
	const U64 to = 1ULL << move.to;
	const U64 from = 1ULL << move.from;
	pos.color[0] ^= from | to;
	pos.pieces[piece] ^= from | to;
	if (piece == PAWN && to == pos.ep) {
		pos.color[1] ^= to >> 8;
		pos.pieces[PAWN] ^= to >> 8;
	}

	pos.ep = 0x0ULL;
	if (piece == PAWN && move.to - move.from == 16) {
		pos.ep = to >> 8;
	}
	if (captured != PT_NB) {
		pos.color[1] ^= to;
		pos.pieces[captured] ^= to;
	}
	if (piece == KING) {
		const U64 bb = move.to - move.from == 2 ? 0xa0ULL : move.to - move.from == -2 ? 0x9ULL : 0x0ULL;
		pos.color[0] ^= bb;
		pos.pieces[ROOK] ^= bb;
	}
	if (piece == PAWN && move.to >= 56) {
		pos.pieces[PAWN] ^= to;
		pos.pieces[move.promo] ^= to;
	}
	pos.castling[0] &= !((from | to) & 0x90ULL);
	pos.castling[1] &= !((from | to) & 0x11ULL);
	pos.castling[2] &= !((from | to) & 0x9000000000000000ULL);
	pos.castling[3] &= !((from | to) & 0x1100000000000000ULL);

	FlipPosition(pos);
	return !Attacked(pos, (int)LSB(pos.color[1] & pos.pieces[KING]), false);
}

static void add_move(Move* const movelist, int& num_moves, const U8 from, const U8 to, const U8 promo = PT_NB) {
	movelist[num_moves++] = Move{ from, to, promo };
}

static void generate_pawn_moves(Move* const movelist, int& num_moves, U64 to_mask, const int offset) {
	while (to_mask) {
		const int to = (int)LSB(to_mask);
		to_mask &= to_mask - 1;
		if (to >= 56) {
			add_move(movelist, num_moves, to + offset, to, QUEEN);
			add_move(movelist, num_moves, to + offset, to, ROOK);
			add_move(movelist, num_moves, to + offset, to, BISHOP);
			add_move(movelist, num_moves, to + offset, to, KNIGHT);
		}
		else {
			add_move(movelist, num_moves, to + offset, to);
		}
	}
}

static void generate_piece_moves(Move* const movelist, int& num_moves, const Position& pos, const int piece, const U64 to_mask, U64(*func)(int, U64)) {
	U64 copy = pos.color[0] & pos.pieces[piece];
	while (copy) {
		const int fr = LSB(copy);
		copy &= copy - 1;
		U64 moves = func(fr, pos.color[0] | pos.color[1]) & to_mask;
		while (moves) {
			const int to = LSB(moves);
			moves &= moves - 1;
			add_move(movelist, num_moves, fr, to);
		}
	}
}

static int MoveGen(const Position& pos, Move* const movelist, const bool only_captures) {
	int num_moves = 0;
	const U64 all = pos.color[0] | pos.color[1];
	const U64 to_mask = only_captures ? pos.color[1] : ~pos.color[0];
	const U64 pawns = pos.color[0] & pos.pieces[PAWN];
	generate_pawn_moves(
		movelist, num_moves, North(pawns) & ~all & (only_captures ? 0xFF00000000000000ULL : 0xFFFFFFFFFFFF0000ULL), -8);
	if (!only_captures) {
		generate_pawn_moves(movelist, num_moves, North(North(pawns & 0xFF00ULL) & ~all) & ~all, -16);
	}
	generate_pawn_moves(movelist, num_moves, NW(pawns) & (pos.color[1] | pos.ep), -7);
	generate_pawn_moves(movelist, num_moves, NE(pawns) & (pos.color[1] | pos.ep), -9);
	generate_piece_moves(movelist, num_moves, pos, KNIGHT, to_mask, KnightAttack);
	generate_piece_moves(movelist, num_moves, pos, BISHOP, to_mask, BishopAttack);
	generate_piece_moves(movelist, num_moves, pos, QUEEN, to_mask, BishopAttack);
	generate_piece_moves(movelist, num_moves, pos, ROOK, to_mask, RookAttack);
	generate_piece_moves(movelist, num_moves, pos, QUEEN, to_mask, RookAttack);
	generate_piece_moves(movelist, num_moves, pos, KING, to_mask, KingAttack);
	if (!only_captures && pos.castling[0] && !(all & 0x60ULL) && !Attacked(pos, 4) && !Attacked(pos, 5)) {
		add_move(movelist, num_moves, 4, 6);
	}
	if (!only_captures && pos.castling[1] && !(all & 0xEULL) && !Attacked(pos, 4) && !Attacked(pos, 3)) {
		add_move(movelist, num_moves, 4, 2);
	}
	return num_moves;
}

static constexpr U64 Attacks(int pt, int sq, U64 blockers) {
	switch (pt) {
	case ROOK:
		return RookAttack(sq, blockers);
	case BISHOP:
		return BishopAttack(sq, blockers);
	case QUEEN:
		return RookAttack(sq, blockers) | BishopAttack(sq, blockers);
	case KNIGHT:
		return KnightAttack(sq, blockers);
	case KING:
		return KingAttack(sq, blockers);
	default:
		return 0;
	}
}

static auto GetHash(const Position& pos) {
	U64 hash = pos.flipped;
	U64 copy = pos.color[0] | pos.color[1];
	while (copy) {
		const int sq = LSB(copy);
		copy &= copy - 1;
		hash ^= keys[(PieceTypeOn(pos, sq) + 6 * ((pos.color[pos.flipped] >> sq) & 1)) * 64 + sq];
	}
	if (pos.ep)
		hash ^= keys[768 + LSB(pos.ep)];
	hash ^= keys[832 + (pos.castling[0] | pos.castling[1] << 1 | pos.castling[2] << 2 | pos.castling[3] << 3)];
	return hash;
}

static void CheckUp() {
	if ((info.timeLimit && GetTimeMs() - info.timeStart > info.timeLimit) || (info.nodesLimit && info.nodes > info.nodesLimit))
		info.stop = true;
}

static bool IsPseudolegalMove(const Position& pos, const Move& move) {
	Move moves[256];
	const int num_moves = MoveGen(pos, moves, false);
	for (int i = 0; i < num_moves; ++i)
		if (moves[i] == move)
			return true;
	return false;
}

static void PrintPv(const Position& pos, const Move move) {
	if (!IsPseudolegalMove(pos, move))
		return;
	auto npos = pos;
	if (!MakeMove(npos, move))
		return;
	cout << " " << MoveToUci(move, pos.flipped);
	const U64 tt_key = GetHash(npos);
	const TT_Entry& tt_entry = transposition_table[tt_key % num_tt_entries];
	if (tt_entry.key != tt_key || tt_entry.move == Move{} || tt_entry.flag != EXACT)
		return;
	if (IsRepetition(pos, tt_key))
		return;
	hash_history[hash_count++] = tt_key;
	PrintPv(npos, tt_entry.move);
	hash_count--;
}

static int Popcount(const U64 bb) {
	return (int)__popcnt64(bb);
}

static int Permill() {
	int pm = 0;
	for (int n = 0; n < 1000; n++) {
		if (transposition_table[n].key)
			pm++;
	}
	return pm;
}

//prints the bitboard
static void PrintBitboard(U64 bb) {
	const char* s = "   +---+---+---+---+---+---+---+---+\n";
	const char* t = "     A   B   C   D   E   F   G   H\n";
	cout << t;
	for (int i = 56; i >= 0; i -= 8) {
		cout << s << " " << i / 8 + 1 << " ";
		for (int x = 0; x < 8; x++) {
			const char* c = 1LL << (i + x) & bb ? "x" : " ";
			cout << "| " << c << " ";
		}
		cout << "| " << i / 8 + 1 << endl;
	}
	cout << s;
	cout << t << endl;
}

static int EvalPosition(Position& pos) {
	int score = 0;
	U64 bbBlockers = pos.color[0] | pos.color[1];
	for (S32 c = WHITE; c < COLOR_NB; ++c) {
		for (int pt = PAWN; pt < KING; ++pt)
			score += material[pt] * Count(pos.color[0] & pos.pieces[pt]);
		U64 bbStart1 = pos.color[1] & pos.pieces[PAWN];
		U64 bbControl1 = SW(bbStart1) | SE(bbStart1);
		score -= Count(bbControl1);
		U64 bbStart0 = pos.color[0] & pos.pieces[KNIGHT];
		U64 bbAttack0 = BbKnightAttack(bbStart0) & ~bbControl1;
		score += Count(bbAttack0);
		bbStart0 = pos.color[0] & (pos.pieces[BISHOP] | pos.pieces[QUEEN]);
		bbAttack0 = BbBishopAttack(bbStart0, bbBlockers) & ~bbControl1;
		score += Count(bbAttack0);
		bbStart0 = pos.color[0] & (pos.pieces[ROOK] | pos.pieces[QUEEN]);
		bbAttack0 = BbRookAttack(bbStart0, bbBlockers) & ~bbControl1;
		score += Count(bbAttack0);
		bbStart0 = pos.color[0] & pos.pieces[KING];
		U64 file0 = filesBB[LSB(bbStart0) % 8];
		file0 |= East(file0) | West(file0);
		bbAttack0 = file0 & (Rank2BB | Rank3BB) & ~(FileDBB | FileEBB);
		bbAttack0 &= (pos.color[0] & pos.pieces[PAWN]);
		score += Count(bbAttack0);
		score += Count(bbAttack0 & Rank2BB);
		FlipPosition(pos);
		score = -score;
	}
	return score;
}

static int SearchAlpha(Position& pos, int alpha, const int beta, S16 depth, const int ply, Stack* const stack) {
	if ((++info.nodes & 0xffff) == 0)
		CheckUp();
	if (info.stop)
		return 0;
	const int static_eval = EvalPosition(pos);
	if (ply > 127)
		return static_eval;
	const auto in_check = Attacked(pos, (int)LSB(pos.color[0] & pos.pieces[KING]));
	if (in_check)
		depth++;
	bool in_qsearch = (depth <= 0 && !in_check);
	if (in_qsearch) {
		if (alpha < static_eval)
			alpha = static_eval;
		if (alpha >= beta)
			return beta;
	}
	const U64 tt_key = GetHash(pos);
	if (ply > 0 && !in_qsearch)
		if (IsRepetition(pos, tt_key))
			return 0;

	TT_Entry& tt_entry = transposition_table[tt_key % num_tt_entries];
	Move tt_move{};
	if (tt_entry.key == tt_key) {
		tt_move = tt_entry.move;
		if (ply > 0 && tt_entry.depth >= depth) {
			if (tt_entry.flag == EXACT)
				return tt_entry.score;
			if (tt_entry.flag == LOWER && tt_entry.score <= alpha)
				return tt_entry.score;
			if (tt_entry.flag == UPPER && tt_entry.score >= beta)
				return tt_entry.score;
		}
	}
	else if (depth > 3)
		depth--;
	int num_moves_quiet = 0;
	int num_moves_evaluated = 0;
	auto& moves = stack[ply].moves;
	auto& moves_scores = stack[ply].moves_scores;
	auto& moves_evaluated = stack[ply].moves_evaluated;
	const int num_moves = MoveGen(pos, moves, in_qsearch);
	for (int j = 0; j < num_moves; ++j) {
		const int capture = PieceTypeOn(pos, moves[j].to);
		if (moves[j] == tt_move) {
			moves_scores[j] = 1LL << 62;
		}
		else if (capture != PT_NB) {
			moves_scores[j] = ((capture + 1) * (1LL << 54)) - PieceTypeOn(pos, moves[j].from);
		}
		else if (moves[j] == stack[ply].killer) {
			moves_scores[j] = 1LL << 50;
		}
		else {
			moves_scores[j] = hh_table[pos.flipped][moves[j].from][moves[j].to];
		}
	}
	S16 best_score = -INF;
	Move best_move{};
	U8 tt_flag = LOWER;
	hash_history[hash_count++] = tt_key;
	for (int i = 0; i < num_moves; ++i) {
		int best_move_index = i;
		for (int j = i + 1; j < num_moves; ++j) {
			if (moves_scores[j] > moves_scores[best_move_index]) {
				best_move_index = j;
			}
		}
		const auto move = moves[best_move_index];
		const auto best_move_score = moves_scores[best_move_index];
		moves[best_move_index] = moves[i];
		moves_scores[best_move_index] = moves_scores[i];
		auto npos = pos;
		if (!MakeMove(npos, move))
			continue;
		int score = -SearchAlpha(npos, -beta, -alpha, depth - 1, ply + 1, stack);
		if (info.stop) {
			hash_count--;
			return 0;
		}
		if (score > best_score) {
			best_score = score;
			best_move = move;
			if (score > alpha) {
				tt_flag = EXACT;
				alpha = score;
				stack[ply].move = move;
				if (!ply) {
					cout << "info";
					cout << " depth " << depth;
					if (abs(score) < MATE - MAX_DEPTH)
						cout << " score cp " << score;
					else
						cout << " score mate " << (score > 0 ? (MATE - score + 1) >> 1 : -(MATE + score) >> 1);
					const auto elapsed = GetTimeMs() - info.timeStart;
					cout << " time " << elapsed;
					cout << " nodes " << info.nodes;
					cout << " hashfull " << Permill();
					cout << " pv";
					PrintPv(pos, stack[0].move);
					cout << endl;
				}
			}
		}
		if (alpha >= beta) {
			tt_flag = UPPER;
			const int capture = PieceTypeOn(pos, move.to);
			if (capture == PT_NB) {
				hh_table[pos.flipped][move.from][move.to] += depth * depth;
				stack[ply].killer = move;
			}
			break;
		}
	}
	hash_count--;
	if (best_score == -INF)
		return in_qsearch ? alpha : in_check ? ply - MATE : 0;
	if (tt_entry.key != tt_key || depth >= tt_entry.depth || tt_flag == EXACT)
		tt_entry = TT_Entry{ tt_key, best_move == no_move ? tt_move : best_move, tt_flag, best_score, in_qsearch ? 0 : depth };
	return alpha;
}

static Move SearchIteratively(Position& pos) {
	memset(stack, 0, sizeof(stack));
	memset(transposition_table, 0, sizeof(transposition_table));
	for (int depth = 1; depth <= info.depthLimit; ++depth) {
		SearchAlpha(pos, -MATE, MATE, depth, 0, stack);
		if (info.stop)
			break;
		if (info.timeLimit && GetTimeMs() - info.timeStart > info.timeLimit / 2) {
			break;
		}
	}
	return stack[0].move;
}

static void SetFen(Position& pos, const string& fen) {
	pos.flipped = false;
	pos.ep = 0;
	memset(pos.color, 0, sizeof(pos.color));
	memset(pos.pieces, 0, sizeof(pos.pieces));
	memset(pos.castling, 0, sizeof(pos.castling));
	stringstream ss(fen);
	string word;
	ss >> word;
	int i = 56;
	for (const auto c : word) {
		if (c >= '1' && c <= '8')
			i += c - '1' + 1;
		else if (c == '/')
			i -= 16;
		else {
			const int side = c == 'p' || c == 'n' || c == 'b' || c == 'r' || c == 'q' || c == 'k';
			const int piece = (c == 'p' || c == 'P') ? PAWN
				: (c == 'n' || c == 'N') ? KNIGHT
				: (c == 'b' || c == 'B') ? BISHOP
				: (c == 'r' || c == 'R') ? ROOK
				: (c == 'q' || c == 'Q') ? QUEEN
				: KING;
			pos.color[side] ^= 1ULL << i;
			pos.pieces[piece] ^= 1ULL << i;
			i++;
		}
	}
	ss >> word;
	const bool black_move = word == "b";
	ss >> word;
	for (const auto c : word) {
		pos.castling[0] |= c == 'K';
		pos.castling[1] |= c == 'Q';
		pos.castling[2] |= c == 'k';
		pos.castling[3] |= c == 'q';
	}
	ss >> word;
	if (word != "-") {
		const int sq = word[0] - 'a' + 8 * (word[1] - '1');
		pos.ep = 1ULL << sq;
	}
	if (black_move)
		FlipPosition(pos);
}

static void PrintBoard(Position& pos) {
	Position np = pos;
	if (np.flipped)
		FlipPosition(np);
	const char* s = "   +---+---+---+---+---+---+---+---+\n";
	const char* t = "     A   B   C   D   E   F   G   H\n";
	cout << t;
	for (int i = 56; i >= 0; i -= 8) {
		cout << s << " " << i / 8 + 1 << " ";
		for (int j = 0; j < 8; j++) {
			int sq = i + j;
			int piece = PieceTypeOn(np, sq);
			if (np.color[0] & 1ull << sq)
				cout << "| " << "ANBRQK "[piece] << " ";
			else
				cout << "| " << "anbrqk "[piece] << " ";
		}
		cout << "| " << i / 8 + 1 << endl;
	}
	cout << s;
	cout << t << endl;
	char castling[5] = "KQkq";
	for (int n = 0; n < 4; n++)
		if (!np.castling[n])
			castling[n] = '-';
	printf("side     : %10s\n", pos.flipped ? "black" : "white");
	printf("castling : %10s\n", castling);
}

static void ParsePosition(string command) {
	string fen = START_FEN;
	stringstream ss(command);
	string token;
	ss >> token;
	if (token != "position")
		return;
	ss >> token;
	if (token == "startpos")
		ss >> token;
	else if (token == "fen") {
		fen = "";
		while (ss >> token && token != "moves")
			fen += token + " ";
		fen.pop_back();
	}
	hash_count = 0;
	SetFen(pos, fen);
	while (ss >> token) {
		Move m = UciToMove(token, pos.flipped);
		MakeMove(pos, m);
	}
}

static void ParseGo(string command) {
	stringstream ss(command);
	string token;
	ss >> token;
	if (token != "go")
		return;
	info.stop = false;
	info.nodes = 0;
	info.depthLimit = 64;
	info.nodesLimit = 0;
	info.timeLimit = 0;
	info.timeStart = GetTimeMs();
	int wtime = 0;
	int btime = 0;
	int winc = 0;
	int binc = 0;
	int movestogo = 32;
	while (ss >> token) {
		if (token == "wtime") {
			ss >> wtime;
		}
		else if (token == "btime") {
			ss >> btime;
		}
		else if (token == "winc") {
			ss >> winc;
		}
		else if (token == "binc") {
			ss >> binc;
		}
		else if (token == "movestogo") {
			ss >> movestogo;
		}
		else if (token == "movetime") {
			ss >> info.timeLimit;
		}
		else if (token == "depth") {
			ss >> info.depthLimit;
		}
		else if (token == "nodes") {
			ss >> info.nodesLimit;
		}
	}
	int time = pos.flipped ? btime : wtime;
	int inc = pos.flipped ? binc : winc;
	if (time)
		info.timeLimit = min(time / movestogo + inc, time / 2);
}

static void UciCommand(string command) {
	if (command.empty())
		return;
	if (command == "uci")
	{
		cout << "id name " << NAME << endl;
		cout << "uciok" << endl;
	}
	else if (command == "isready")
		cout << "readyok" << endl;
	else if (command == "ucinewgame")
		memset(hh_table, 0, sizeof(hh_table));
	else if (command.substr(0, 8) == "position")
		ParsePosition(command);
	else if (command.substr(0, 2) == "go") {
		ParseGo(command);
		const Move best_move = SearchIteratively(pos);
		cout << "bestmove " << MoveToUci(best_move, pos.flipped) << endl << flush;
	}
	//else if (command == "print")PrintBoard(pos);
	else if (command == "quit")
		exit(0);
}

static void UciLoop() {
	string line;
	while (true) {
		getline(cin, line);
		UciCommand(line);
	}
}

int main(const int argc, const char** argv) {
	cout << NAME << " " << VERSION << endl;
	mt19937_64 r;
	for (U64& k : keys)
		k = r();
	SetFen(pos, START_FEN);
	UciLoop();
}
