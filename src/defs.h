// LICENSE
// This software is free for use and redistribution while including this
// license notice, unless:
// 1. is used for commercial or non-personal purposes, or
// 2. used for a product which includes or associated with a blockchain or other
// decentralized database technology, or
// 3. used for a product which includes or associated with the issuance or use
// of cryptographic or electronic currencies/coins/tokens.
// On all of the mentioned cases, an explicit and written permission is required
// from the Author (Ohad Asor).
// Contact ohad@idni.org for requesting a permission. This license may be
// modified over time by the Author.
#ifndef __DEFS_H__
#define __DEFS_H__
#include <cassert>
#include <vector>
#include <set>
#include <unordered_map>
#include <array>
#include <iostream>
#include <cstdio>

#ifdef __EMSCRIPTEN__
typedef int32_t int_t;
#define BDD_HASH_H_SHIFT 7
#define BDD_HASH_L_SHIFT 20
#else
#include <execinfo.h>
typedef int64_t int_t;
#define BDD_HASH_H_SHIFT 13
#define BDD_HASH_L_SHIFT 40
#endif

typedef wchar_t* wstr;
typedef const wchar_t* cws;
typedef cws* pcws;
typedef std::array<cws, 2> lexeme;
typedef std::vector<lexeme> lexemes;
typedef std::vector<int_t> ints;
typedef std::unordered_map<int_t, std::wstring> strs_t;
typedef std::vector<bool> bools;
typedef std::vector<bools> vbools;
typedef std::vector<size_t> sizes;

//#define DEEPDEBUG
#ifdef DEBUG
#define DBG(x) x
#define NDBG(x)
#else
#define DBG(x)
#define NDBG(x) x
#endif
#define er(x)	wcerr<<x<<endl, exit(0)
#define msb(x) ((sizeof(unsigned long long)<<3) - \
	__builtin_clzll((unsigned long long)(x)))
#define POS(bit, bits, arg, args) ((bits - (bit) - 1) * (args) + (arg))
#define ARG(pos, args) ((pos) % (args))
#define BIT(pos, args, bits) (bits - ((pos) / (args)) - 1)
#define has(x, y) ((x).find(y) != (x).end())
#define hasb(x, y) std::binary_search(x.begin(), x.end(), y)
template<typename T> T sort(const T& x){T t=x;return sort(t.begin(),t.end()),t;}
void parse_error(std::wstring e, lexeme l);
struct lexcmp { bool operator()(const lexeme& x, const lexeme& y) const; };
void dump_stack();
#endif