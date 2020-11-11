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
#include "defs.h"

struct term : public ints {
	bool neg = false, goal = false;
	//XXX: ARITH is also a formula, likely should be handled
	//     along logic formulas FORM1, FORM2:SO[HORN], SO[KROM]

	//FIXME: warning, there is direct assignment between these two enums in from_raw_term
	// enum rtextype { REL, EQ, LEQ, BLTIN, ARITH, CONSTRAINT }
	enum textype { REL, EQ, LEQ, BLTIN, ARITH, FORM1 /*QBF1*/, FORM2} extype = term::REL;

	t_arith_op arith_op = NOP;
	spform_handle qbf;

	// The id of the table associated with the fact/rule referenced by this term
	ntable tab = -1;
	size_t orderid = 0;

	// D: TODO: builtins are very different, handle as a same size union struct?
	int_t idbltin = -1; // size_t bltinsize;
	term() {}

	term(bool neg, textype extype, t_arith_op arith_op, ntable tab, const ints& args, size_t orderid)
		: ints(args), neg(neg),extype(extype), arith_op(arith_op), tab(tab), orderid(orderid) {}

	term(textype extype, std::shared_ptr<form> qbf): extype(extype), qbf(std::move(qbf)) {};

	// builtins .ctor
	term(bool neg, ntable tab, const ints& args, size_t orderid, int_t idbltin)
		: ints(args), neg(neg), extype(term::BLTIN), tab(tab), orderid(orderid),
		idbltin(idbltin) {}

	bool operator<(const term& t) const {
		if (neg != t.neg) return neg;
		//if (extype != t.extype) return extype < t.extype;
		if (tab != t.tab) return tab < t.tab;
		if (qbf != t.qbf) return qbf < t.qbf;
		if (goal != t.goal) return goal;
		return (const ints&)*this < t;
	}
	void replace(const std::map<int_t, int_t>& m);
};

template <typename T>
std::basic_ostream<T>& operator<<(std::basic_ostream<T>& os, const term& t);
std::vector<term> to_vec(const term& h, const std::set<term>& b);
template<typename T> std::set<T> vec2set(const std::vector<T>& v, size_t n = 0);
