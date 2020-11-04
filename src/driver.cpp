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
#include <map>
#include <set>
#include <string>
#include <cstring>
#include <sstream>
#include <forward_list>
#include <functional>
#include <cctype>
#include <ctime>
#include <locale>
#include <codecvt>
#include <fstream>
#include "driver.h"
#include "err.h"
#include "archive.h"

#ifdef __EMSCRIPTEN__
#include "../js/embindings.h"
#endif

using namespace std;

template <typename T>
std::basic_ostream<T>& operator<<(std::basic_ostream<T>& os, const pair<ccs, size_t>& p);

void driver::transform_len(raw_term& r, const strs_t& s) {
	for (size_t n = 1; n < r.e.size(); ++n)
		if (	r.e[n].type == elem::SYM && r.e[n].e == "len" &&
			n+3 < r.e.size() &&
			r.e[n+1].type == elem::OPENP &&
			r.e[n+2].type == elem::SYM &&
			r.e[n+3].type == elem::CLOSEP) {
			auto it = s.find(r.e[n+2].e);
			int_t len = it == s.end() ? 0 : it->second.size();
//			if (it == s.end()) parse_error(err_len, r.e[n+2].e);
			r.e.erase(r.e.begin()+n,r.e.begin()+n+4),
			r.e.insert(r.e.begin()+n, elem(len)),
			r.calc_arity(current_input);
		}
}

size_t driver::load_stdin() {
	ostringstream_t ss; ss << CIN.rdbuf();
	pd.std_input = to_string_t(ws2s(ss.str()));
	return pd.std_input.size();
}

void unquote(string_t& str);

string_t driver::directive_load(const directive& d) {
	string_t str(d.arg[0]+1, d.arg[1]-d.arg[0]-2);
	switch (d.type) {
		case directive::FNAME:
			return to_string_t(input::file_read(to_string(str)));
		case directive::STDIN: return move(pd.std_input);
		default: return unquote(str), str;
	}
	DBGFAIL;
}

void driver::directives_load(raw_prog& p, lexeme& trel) {
//	int_t rel;
	for (const directive& d : p.d)
		switch (d.type) {
		case directive::BWD: pd.bwd = true; break;
		case directive::TRACE: trel = d.rel.e; break;
		case directive::CMDLINE:
			if (d.n < opts.argc())
				pd.strs.emplace(d.rel.e,
					to_string_t(opts.argv(d.n)));
			else parse_error(err_num_cmdline);
			break;
/*		case directive::STDOUT: pd.out.push_back(get_term(d.t,pd.strs));
					break;
		case directive::TREE:
			rel = dict.get_rel(d.t.e[0].e);
			if (has(pd.strtrees, rel) || has(pd.strs, rel))
				parse_error(err_str_defined, d.t.e[0].e);
			else pd.strtrees.emplace(rel, get_term(d.t,pd.strs));
			break;*/
		default: pd.strs.emplace(d.rel.e, directive_load(d));
		}
}

/* Copys the given elem taking care to change its variable name
 * according to the supplied map if it is a variable. If the variable is
 * not found in the map, then a fresh one is generated. */

elem driver::hygienic_copy(const elem &e, std::map<elem, elem> &vars) {
	// Get dictionary for generating fresh variables
	dict_t &d = tbl->get_dict();
	if(e.type == elem::VAR) {
		if(vars.find(e) != vars.end()) {
			return vars[e];
		} else {
			// Since the current variable lacks a designated substitute,
			// make one and record the mapping.
			return vars[e] = elem::fresh_var(d);
		}
	} else {
		return e;
	}
}

/* Copys the given raw_term taking care to change all variable names
 * according to the supplied map. If a variable is not found in the map,
 * then a fresh one is generated. */

raw_term driver::hygienic_copy(raw_term rt, std::map<elem, elem> &vars) {
	for(elem &e : rt.e) {
		e = hygienic_copy(e, vars);
	}
	return rt;
}

/* Copys the given sprawformtree taking care to change all variable names
 * according to the supplied map. If a variable is not found in the map,
 * then a fresh one is generated. */

sprawformtree driver::hygienic_copy(sprawformtree &rft,
		std::map<elem, elem> &vars) {
	switch(rft->type) {
		case elem::IMPLIES: case elem::COIMPLIES: case elem::AND:
		case elem::ALT:
			return std::make_shared<raw_form_tree>(rft->type,
				hygienic_copy(rft->l, vars), hygienic_copy(rft->r, vars));
		case elem::NOT:
			return std::make_shared<raw_form_tree>(elem::NOT,
				hygienic_copy(rft->l, vars));
		case elem::EXISTS: case elem::UNIQUE: case elem::FORALL:  {
			elem elt = hygienic_copy(*(rft->l->el), vars);
			return std::make_shared<raw_form_tree>(rft->type,
				std::make_shared<raw_form_tree>(elem::VAR, elt), 
				hygienic_copy(rft->r, vars));
		} case elem::NONE:
			return std::make_shared<raw_form_tree>(elem::NONE,
				hygienic_copy(*rft->rt, vars));
		default:
			assert(false); //should never reach here
	}
}

/* Takes a term to be expanded, the rule that is to be inlined at its
 * location, the specific head of the rule that is to be applied, and
 * uses the rule's body to generate a formula equivalent (if we ignore
 * the possiblity of other substitutions) to the unexpanded term. */

sprawformtree driver::inline_rule(const raw_term &rt1, const raw_term &rt2,
		const raw_rule &rr) {
	if(rt1.e.size() == rt2.e.size()) {
		std::set<std::tuple<elem, elem>> constraints;
		for(size_t i = 0; i < rt1.e.size(); i++) {
			if(rt1.e[i].type != elem::VAR || rt2.e[i].type == elem::VAR) {
				constraints.insert({rt1.e[i], rt2.e[i]});
			} else if(rt1.e[i] != rt2.e[i]) {
				return nullptr;
			}
		}
		std::map<elem, elem> var_map;
		sprawformtree tmp = rr.prft;
		sprawformtree copy = hygienic_copy(tmp, var_map);
		for(const auto &[el1, el2] : constraints) {
			copy = std::make_shared<raw_form_tree>(elem::AND, copy,
				std::make_shared<raw_form_tree>(elem::NONE,
					raw_term({el1, elem_eq, var_map[el2]})));
		}
		return copy;
	} else {
		return nullptr;
	}
}

/* If the relation in the given term is in the set of inlines, then
 * substitute this term with the body of the corresponding rule with
 * sufficient variable hygiene. If there is more than one possible rule,
 * then disjunct them together. */

sprawformtree driver::inline_rule(const raw_term &rt,
		const std::vector<raw_rule> &inlines) {
	sprawformtree unfolded_tree = nullptr;
	for(const raw_rule &idb : inlines) {
		for(const raw_term &hd : idb.h) {
			sprawformtree tree_disj = inline_rule(rt, hd, idb);
			if(unfolded_tree && tree_disj) {
				unfolded_tree = std::make_shared<raw_form_tree>(elem::ALT,
					unfolded_tree, tree_disj);
			} else if(tree_disj) {
				unfolded_tree = tree_disj;
			}
		}
	}
	return unfolded_tree;
}

/* Checks if the given formula is conjunctive, that is, ultimately a
 * tree of conjunctions of terms. If so, then put the terms that are
 * ultimately conjuncted into the list. Note that if the body of a query
 * is a conjunctive formula, then the query is also conjunctive. */

bool driver::is_formula_conjunctive(const sprawformtree &tree,
		std::vector<raw_term> &tms, std::map<elem, elem> &variables) {
	// Get dictionary for generating fresh variables
	dict_t &d = tbl->get_dict();
	
	if(tree->type == elem::NONE) {
		tms.push_back(hygienic_copy(*tree->rt, variables));
		return true;
	} else if(tree->type == elem::AND) {
		return is_formula_conjunctive(tree->l, tms, variables) &&
			is_formula_conjunctive(tree->r, tms, variables);
	} else if(tree->type == elem::EXISTS) {
		elem elt = *(tree->l->el);
		std::optional<elem> prev_map = at_optional(variables, elt);
		variables[elt] = elem::fresh_var(d);
		bool ans = is_formula_conjunctive(tree->r, tms, variables);
		insert_optional(variables, elt, prev_map);
		return ans;
	} else {
		return false;
	}
}

/* Checks if the body of the given rule is conjunctive. If so, then
 * return the terms that are ultimately conjuncted into a list. */

bool driver::is_rule_conjunctive(const raw_rule &rr,
		std::vector<raw_term> &hds, std::vector<raw_term> &tms) {
	std::map<elem, elem> variables;
	for(const raw_term &rt : rr.h) {
		hds.push_back(hygienic_copy(rt, variables));
	}
	return is_formula_conjunctive(rr.prft, tms, variables);
}

sprawformtree driver::make_cqc_constraints(std::vector<raw_term> terms1,
		std::map<elem, elem> map1, std::vector<raw_term> terms2,
		std::map<elem, elem> map2) {
	sprawformtree conj = std::make_shared<raw_form_tree>(elem::NONE, ttrue);
	for(const raw_term &tm2 : terms2) {
		sprawformtree disj =
			std::make_shared<raw_form_tree>(elem::NONE, tfalse);
		for(const raw_term &tm1 : terms1) {
			if(tm1.e[0] == tm2.e[0] && tm1.e.size() == tm2.e.size()) {
				sprawformtree constraint =
					std::make_shared<raw_form_tree>(elem::NONE, ttrue);
				for(size_t i = 2; i < tm1.e.size() - 1; i++) {
					constraint = std::make_shared<raw_form_tree>(elem::AND,
						constraint,
						std::make_shared<raw_form_tree>(elem::NONE,
							raw_term(raw_term::EQ,
								{at_default(map2, tm2.e[i], tm2.e[i]), elem_eq,
									at_default(map1, tm1.e[i], tm1.e[i])})));
				}
				disj = std::make_shared<raw_form_tree>(elem::ALT, disj,
					constraint);
			}
		}
		conj = std::make_shared<raw_form_tree>(elem::AND, conj, disj);
	}
	return conj;
}

bool driver::cqc(const raw_rule &rr1, const raw_rule &rr2) {
	dict_t &d = tbl->get_dict();
	std::vector<raw_term> heads1, bodie1, heads2, bodie2;
	// The rules must be conjunctive as per precondition
	if(is_rule_conjunctive(rr1, heads1, bodie1) &&
			is_rule_conjunctive(rr2, heads2, bodie2)) {
		// The terms of the conjunctive queries must also be uninterpreted
		for(const raw_term &rt : bodie1) {
			if(rt.extype != raw_term::REL) return false;
		}
		for(const raw_term &rt : bodie2) {
			if(rt.extype != raw_term::REL) return false;
		}
		// Freeze the variables and symbols of the rule we are checking the
		// containment of
		std::map<elem, elem> freeze_map;
		freeze_vars(heads1, freeze_map);
		freeze_vars(bodie1, freeze_map);
		
		// Encode the constraint that there is a homomorphism from rule 2
		// to the frozen rule 1
		sprawformtree constraints =
			std::make_shared<raw_form_tree>(elem::AND,
				make_cqc_constraints(bodie1, freeze_map, bodie2, {}),
				make_cqc_constraints(heads2, {}, heads1, freeze_map));
		
		// Make a head for these constrain equations. We don't actually need
		// the homomorphism though, so an empty head is fine.
		std::vector<elem> head_e =
			{ elem::fresh_sym(d), elem_openp, elem_closep };
		
		// Make the constraint rule and solve it
		raw_rule cqc_rule = raw_rule(raw_term(head_e), constraints);
		raw_prog nrp;
		nrp.r = {cqc_rule};
		simplify_formulas(nrp);
		insert_exists(nrp);
		std::set<elem> universe;
		std::set<raw_term> database;
		naive_pfp(nrp, universe, database);
		
		// The presence of at least one result proves existence of
		// homomorphism
		return !database.empty();
	} else {
		return false;
	}
}

bool driver::try_cqc_strip(raw_rule &rr) {
	std::vector<raw_term> heads1, bodie1, heads2, bodie2;
	if(is_rule_conjunctive(rr, heads1, bodie1)) {
		heads2 = heads1;
		bodie2 = bodie1;
		for(size_t i = 0; i < bodie1.size(); i++) {
			// bodie2 is currently equal to bodie1
			bodie2.erase(bodie2.begin() + i);
			// bodie2 missing element i, meaning that rule 2 contains rule 1
			// Construct our candidate replacement rule
			raw_rule rr2(heads2, bodie2);
			simplify_formula(rr2.prft);
			insert_exists(rr2);
			if(cqc(rr2, rr)) {
				// successful if condition implies rule 1 contains rule 2, hence
				// rule 1 = rule 2
				rr = rr2;
				return true;
			}
			bodie2.insert(bodie2.begin() + i, bodie1[i]);
			// bodie2 is currently equal to bodie1
		}
	}
	return false;
}

void driver::cqc_strip(raw_prog &rp) {
	for(raw_rule &rr : rp.r) {
		while(try_cqc_strip(rr));
	}
}

void driver::simplify_formula(sprawformtree &t) {
	switch(t->type) {
		case elem::IMPLIES:
			simplify_formula(t->l);
			simplify_formula(t->r);
			break;
		case elem::COIMPLIES:
			simplify_formula(t->l);
			simplify_formula(t->r);
			break;
		case elem::AND:
			simplify_formula(t->l);
			simplify_formula(t->r);
			if(t->l->type == elem::NONE && t->l->rt->is_true()) {
				t = t->r;
			} else if(t->r->type == elem::NONE && t->r->rt->is_true()) {
				t = t->l;
			}
			break;
		case elem::ALT:
			simplify_formula(t->l);
			simplify_formula(t->r);
			if(t->l->type == elem::NONE && t->l->rt->is_false()) {
				t = t->r;
			} else if(t->r->type == elem::NONE && t->r->rt->is_false()) {
				t = t->l;
			}
			break;
		case elem::NOT:
			simplify_formula(t->l);
			break;
		case elem::EXISTS: {
			simplify_formula(t->r);
			break;
		} case elem::UNIQUE: {
			simplify_formula(t->r);
			break;
		} case elem::NONE: {
			break;
		} case elem::FORALL: {
			simplify_formula(t->r);
			break;
		} default:
			assert(false); //should never reach here
	}
}

void driver::simplify_formulas(raw_prog &rp) {
	for(raw_rule &rr : rp.r) {
		simplify_formula(rr.prft);
	}
}

/* In the case that the argument is a variable, get the symbol
 * associated with it and return that. If there is no such association,
 * make one. */

elem driver::quote_elem(const elem &e, std::map<elem, elem> &variables) {
	// Get dictionary for generating fresh symbols
	dict_t &d = tbl->get_dict();
	if(e.type == elem::VAR) {
		if(variables.find(e) != variables.end()) {
			return variables[e];
		} else {
			// Since the current variable lacks a designated substitute,
			// make one and record the mapping.
			return variables[e] = elem::fresh_sym(d);
		}
	} else {
		return e;
	}
}

/* Iterate through terms and associate each unique variable with unique
 * fresh symbol. */

void driver::freeze_vars(const std::vector<raw_term> &terms,
		std::map<elem, elem> &freeze_map) {
	for(const raw_term &tm : terms) {
		for(const elem &el : tm.e) {
			quote_elem(el, freeze_map);
		}
	}
}

/* Takes a raw term and returns its quotation within a relation of the
 * given name. The names of variable elements within the raw term are
 * added to the variables map. */

elem driver::quote_term(const raw_term &head, const elem &rel_name,
		raw_prog &rp, std::map<elem, elem> &variables) {
	// Get dictionary for generating fresh symbols
	dict_t &d = tbl->get_dict();
	elem term_id = elem::fresh_sym(d);
	if(head.extype == raw_term::REL) {
		// Add metadata to quoted term: term signature, term id, term name
		std::vector<elem> quoted_term_e = {rel_name, elem_openp, elem(QTERM),
			term_id, head.e[0] };
		
		for(int_t param_idx = 2; param_idx < ssize(head.e) - 1; param_idx ++) {
			quoted_term_e.push_back(quote_elem(head.e[param_idx], variables));
		}
		// Terminate term elements and make raw_term object
		quoted_term_e.push_back(elem_closep);
		rp.r.push_back(raw_rule(raw_term(quoted_term_e)));
	} else if(head.extype == raw_term::EQ) {
		// Add metadata to quoted term: term signature, term id, term name
		std::vector<elem> quoted_term_e = {rel_name, elem_openp, elem(QEQUALS),
			term_id, quote_elem(head.e[0], variables),
			quote_elem(head.e[2], variables), elem_closep };
		rp.r.push_back(raw_rule(raw_term(quoted_term_e)));
	}
	if(head.neg) {
		// If this term is actually negated, then we'll make a parent for
		// this node and return its id
		elem neg_id = elem::fresh_sym(d);
		rp.r.push_back(raw_rule(raw_term({rel_name, elem_openp, elem(QNOT),
			neg_id, term_id, elem_closep})));
		return neg_id;
	} else {
		return term_id;
	}
}

elem driver::quote_formula(const sprawformtree &t, const elem &rel_name,
		raw_prog &rp, std::map<elem, elem> &variables) {
	// Get dictionary for generating fresh symbols
	dict_t &d = tbl->get_dict();
	const elem part_id = elem::fresh_sym(d);
	switch(t->type) {
		case elem::IMPLIES:
			rp.r.push_back(raw_rule(raw_term({rel_name, elem_openp, elem(QIMPLIES),
				part_id, quote_formula(t->l, rel_name, rp, variables),
				quote_formula(t->r, rel_name, rp, variables), elem_closep })));
			break;
		case elem::COIMPLIES:
			rp.r.push_back(raw_rule(raw_term({rel_name, elem_openp, elem(QCOIMPLIES),
				part_id, quote_formula(t->l, rel_name, rp, variables),
				quote_formula(t->r, rel_name, rp, variables), elem_closep })));
			break;
		case elem::AND:
			rp.r.push_back(raw_rule(raw_term({rel_name, elem_openp, elem(QAND),
				part_id, quote_formula(t->l, rel_name, rp, variables),
				quote_formula(t->r, rel_name, rp, variables), elem_closep })));
			break;
		case elem::ALT:
			rp.r.push_back(raw_rule(raw_term({rel_name, elem_openp, elem(QALT),
				part_id, quote_formula(t->l, rel_name, rp, variables),
				quote_formula(t->r, rel_name, rp, variables), elem_closep })));
			break;
		case elem::NOT:
			rp.r.push_back(raw_rule(raw_term({rel_name, elem_openp, elem(QNOT),
				part_id, quote_formula(t->l, rel_name, rp, variables),
				elem_closep })));
			break;
		case elem::EXISTS: {
			elem qvar = quote_elem(*(t->l->el), variables);
			rp.r.push_back(raw_rule(raw_term({rel_name, elem_openp,
				elem(QEXISTS), part_id, qvar,
				quote_formula(t->r, rel_name, rp, variables), elem_closep })));
			break;
		} case elem::UNIQUE: {
			elem qvar = quote_elem(*(t->l->el), variables);
			rp.r.push_back(raw_rule(raw_term({rel_name, elem_openp,
				elem(QUNIQUE), part_id, qvar,
				quote_formula(t->r, rel_name, rp, variables), elem_closep })));
			break;
		} case elem::NONE: {
			return quote_term(*t->rt, rel_name, rp, variables);
			break;
		} case elem::FORALL: {
			elem qvar = quote_elem(*(t->l->el), variables);
			rp.r.push_back(raw_rule(raw_term({rel_name, elem_openp,
				elem(QFORALL), part_id, qvar,
				quote_formula(t->r, rel_name, rp, variables), elem_closep })));
			break;
		} default:
			assert(false); //should never reach here
	}
	return part_id;
}

std::vector<elem> driver::quote_rule(const raw_rule &rr, const elem &rel_name,
		raw_prog &rp, std::map<elem, elem> &variables) {
	// Get dictionary for generating fresh symbols
	dict_t &d = tbl->get_dict();
	std::vector<elem> rule_ids;
	const elem body_id = quote_formula(rr.prft, rel_name, rp, variables);
	for(int_t gidx = 0; gidx < ssize(rr.h); gidx++) {
		const elem head_id = quote_term(rr.h[gidx], rel_name, rp, variables);
		const elem rule_id = elem::fresh_sym(d);
		rp.r.push_back(raw_rule(raw_term({rel_name, elem_openp, elem(QRULE),
			rule_id, head_id, body_id, elem_closep })));
		rule_ids.push_back(rule_id);
	}
	return rule_ids;
}

/* Parse an STR elem into a raw_prog. */

raw_prog driver::read_prog(elem prog, const raw_prog &rp) {
	lexeme prog_str = {prog.e[0]+1, prog.e[1]-1};
	input *prog_in = dynii.add_string(lexeme2str(prog_str));
	prog_in->prog_lex();
	raw_prog nrp;
	nrp.builtins = rp.builtins;
	nrp.parse(prog_in, tbl->get_dict());
	simplify_formulas(nrp);
	return nrp;
}

/* Loop through the rules of the given program checking if they use a
 * function called "quote" in their bodies. Quote's first argument is
 * the relation into which it should put the quotation it creates, and
 * it's second argument is the program to quote. Say that the output
 * relation name is s, quote will populate it according to the following
 * schema:
 * q(VARS <var name>)
 * q(RULE <id> <head id> <body id>).
 * q(TERM <id> <name>).
 * q(TERM <id> <name> <param1 name>).
 * q(TERM <id> <name> <param1 name> <param2 name>).
 * q(TERM <id> <name> <param1 name> <param2 name> <param3 name>).
 * q(TERM <id> <name> <param1 name> <param2 name> <param3 name> <param4 name>).
 * q(EQUALS <id> <param1 name> <param2 name>).
 * q(FORALL <id> <var name> <body id>).
 * q(EXISTS <id> <var name> <body id>).
 * q(NOT <id> <body id>).
 * q(AND <id> <body1 id> <body2 id>).
 * q(OR <id> <body1 id> <body2 id>). */

void driver::transform_quotes(raw_prog &rp) {
	for(size_t oridx = 0; oridx < rp.r.size(); oridx++) {
		// Iterate through the bodies of the current rule looking for uses of the
		// "quote" relation.
		for(raw_term &curr_term : rp.r[oridx].h) {
			// Search for uses of quote within a relation.
			for(int_t offset = 3; offset < ssize(curr_term.e); offset ++) {
				if(curr_term.e[offset].type == elem::STR &&
						curr_term.e[offset].e[1] > curr_term.e[offset].e[0] &&
						*curr_term.e[offset].e[0] == '`') {
					raw_prog nrp = read_prog(curr_term.e[offset], rp);
					// The relation under which the quotation we build will be stored.
					elem rel_name = curr_term.e[offset - 1];
					// Replace the whole quotation with the relation it will create.
					curr_term.e.erase(curr_term.e.begin() + offset);
					curr_term.calc_arity(nullptr);
					// Maintain a list of the variable substitutions:
					std::map<elem, elem> variables;
					for(int_t ridx = 0; ridx < ssize(nrp.r); ridx++) {
						quote_rule(nrp.r[ridx], rel_name, rp, variables);
					}
					// Now create sub-relation to store the names of the variable
					// substitutes in the quoted relation
					for(auto const& [_, var_sym] : variables) {
						rp.r.push_back(raw_rule(raw_term({ rel_name, elem_openp,
							elem(QVARS), var_sym, elem_closep })));
					}
				}
			}
		}
	}
}

sprawformtree driver::fix_variables(const elem &quote_sym,
		const elem &qva, const elem &rva, const elem &qvb, const elem &rvb) {
	return std::make_shared<raw_form_tree>(elem::IMPLIES,
		std::make_shared<raw_form_tree>(elem::AND,
			std::make_shared<raw_form_tree>(elem::AND,
				std::make_shared<raw_form_tree>(elem::NONE,
					raw_term({quote_sym, elem_openp, elem(QVARS), qva, elem_closep})),
				std::make_shared<raw_form_tree>(elem::NONE,
					raw_term({quote_sym, elem_openp, elem(QVARS), qvb, elem_closep}))),
			std::make_shared<raw_form_tree>(elem::NONE,
				raw_term(raw_term::EQ, {qva, elem_eq, qvb}))),
		std::make_shared<raw_form_tree>(elem::NONE, raw_term(raw_term::EQ,
			{rva, elem_eq, rvb})));
}

sprawformtree driver::fix_symbols(const elem &quote_sym,
		const elem &qva, const elem &rva) {
	return std::make_shared<raw_form_tree>(elem::IMPLIES,
		std::make_shared<raw_form_tree>(elem::NOT,
			std::make_shared<raw_form_tree>(elem::NONE,
				raw_term({ quote_sym, elem_openp, elem(QVARS), qva, elem_closep }))),
		std::make_shared<raw_form_tree>(elem::NONE,
			raw_term(raw_term::EQ, {qva, elem_eq, rva})));
}

// Interpret conjunctions with varying allocations to each side
void driver::generate_binary_eval(raw_prog &rp, const int_t qtype,
		const elem::etype &eltype, const elem &quote_sym,
		const elem &und_sym, const elem &aux_rel,
		const std::vector<elem> &iparams, const std::vector<elem> &qparams) {
	// Get dictionary for generating fresh variables
	dict_t &d = tbl->get_dict();
	
	int_t arity_num = qparams.size();
	elem elt_id = elem::fresh_var(d), forma_id = elem::fresh_var(d),
		formb_id = elem::fresh_var(d);
	for(int_t a = 0; a < arity_num+1; a++) {
		std::vector<elem> head_e = { aux_rel, elem_openp, elt_id };
		for(int_t i = 0; i < arity_num; i++) {
			head_e.push_back(qparams[i]);
			head_e.push_back(iparams[i]);
		}
		head_e.push_back(elem_closep);
		raw_term quote({quote_sym, elem_openp, elem(qtype), elt_id,
			forma_id, formb_id, elem_closep });
		std::vector<elem> forma_e = { aux_rel, elem_openp, forma_id };
		for(int_t i = a; i < arity_num; i++) {
			forma_e.push_back(qparams[i]);
			forma_e.push_back(iparams[i]);
		}
		for(int_t i = 0; i < a; i++) {
			forma_e.push_back(und_sym);
			forma_e.push_back(und_sym);
		}
		forma_e.push_back(elem_closep);
		std::vector<elem> formb_e = { aux_rel, elem_openp, formb_id };
		for(int_t i = 0; i < a; i++) {
			formb_e.push_back(qparams[i]);
			formb_e.push_back(iparams[i]);
		}
		for(int_t i = a; i < arity_num; i++) {
			formb_e.push_back(und_sym);
			formb_e.push_back(und_sym);
		}
		formb_e.push_back(elem_closep);
		sprawformtree bodie =
			std::make_shared<raw_form_tree>(elem::AND,
				std::make_shared<raw_form_tree>(elem::NONE, quote),
				std::make_shared<raw_form_tree>(eltype,
					std::make_shared<raw_form_tree>(elem::NONE, raw_term(forma_e)),
					std::make_shared<raw_form_tree>(elem::NONE, raw_term(formb_e))));
		
		for(int_t i = 0; i < a; i++) {
			for(int_t j = a; j < arity_num; j++) {
				bodie = std::make_shared<raw_form_tree>(elem::AND, bodie,
					fix_variables(quote_sym, qparams[i], iparams[i],
						qparams[j], iparams[j]));
			}
		}
		rp.r.push_back(raw_rule(head_e, bodie));
	}
}

void driver::generate_quantified_eval(raw_prog &rp, const int_t qtype,
		const elem::etype &eltype, const elem &quote_sym, const elem &aux_rel,
		const std::vector<elem> &iparams, const std::vector<elem> &qparams) {
	// Get dictionary for generating fresh variables
	dict_t &d = tbl->get_dict();
	
	int_t arity_num = qparams.size();
	const elem quantified_var = elem::fresh_var(d),
		elt_id = elem::fresh_var(d), forma_id = elem::fresh_var(d),
		formb_id = elem::fresh_var(d);
	std::vector<elem> head_e = { aux_rel, elem_openp, elt_id };
	for(int_t i = 0; i < arity_num; i++) {
		head_e.push_back(qparams[i]);
		head_e.push_back(iparams[i]);
	}
	head_e.push_back(elem_closep);
	raw_term quote({quote_sym, elem_openp, elem(qtype), elt_id,
		forma_id, formb_id, elem_closep });
	std::vector<elem> quant_e = { aux_rel, elem_openp, formb_id };
	for(int_t i = 0; i < arity_num; i++) {
		quant_e.push_back(qparams[i]);
		quant_e.push_back(iparams[i]);
	}
	quant_e.push_back(elem_closep);
	sprawformtree quant =
		std::make_shared<raw_form_tree>(elem::NONE, quant_e);
	for(int_t i = 0; i < arity_num; i++) {
		quant = std::make_shared<raw_form_tree>(elem::AND, quant,
			fix_variables(quote_sym, forma_id, quantified_var,
				qparams[i], iparams[i]));
	}
	raw_rule rr(head_e);
	rr.prft = std::make_shared<raw_form_tree>(elem::AND,
		std::make_shared<raw_form_tree>(elem::NONE, quote),
		std::make_shared<raw_form_tree>(eltype,
			std::make_shared<raw_form_tree>(elem::VAR, quantified_var),
			quant));
	rp.r.push_back(rr);
}

/* Loop through the rules of the given program checking if they use a
 * relation called "eval" in their bodies. If eval is used, take its
 * three arguments: the name of the relation that will contain the
 * equivalent of the original TML program, the name of a relation
 * containing the program arity of the relation to be evaluated, and the
 * formal name of a relation containing a representation of a TML program.
 * Note that the evaled relation will only depend on the relation's
 * program arity and its name - not its entries. */

void driver::transform_evals(raw_prog &rp) {
	for(size_t oridx = 0; oridx < rp.r.size(); oridx++) {
		// Iterate through the bodies of the current rule looking for uses
		// of the "eval" relation.
		for(const raw_term &curr_term : rp.r[oridx].h) {
			if(!(!curr_term.e.empty() && curr_term.e[0].type == elem::SYM &&
				to_string_t("eval") == lexeme2str(curr_term.e[0].e))) continue;
			// The first parenthesis marks the beginning of eval's three arguments.
			if(!(ssize(curr_term.e) == 6 && curr_term.e[1].type == elem::OPENP &&
				curr_term.e[5].type == elem::CLOSEP)) continue;
			// The relation to contain the evaled relation is the first symbol
			// between the parentheses
			elem out_rel = curr_term.e[2];
			// The relation containing the quotation arity is the second symbol
			// between the parentheses
			elem arity_num = curr_term.e[3];
			// The formal symbol representing the quotation relation is the
			// third symbol between the parentheses
			elem quote_sym = curr_term.e[4];
			// Get dictionary for generating fresh variables
			dict_t &d = tbl->get_dict();
			// This symbol is used when the variable allocation is finished
			elem und_sym = elem::fresh_sym(d);
			// This relation will house most of the interpreter
			elem aux_rel = elem::fresh_sym(d);
			
			// Interpret the varying rule arities.
			// Allocate rule name, rule id, head id, body id
			elem rule_name = elem::fresh_var(d), head_id = elem::fresh_var(d),
				body_id = elem::fresh_var(d), elt_id = elem::fresh_var(d),
				forma_id = elem::fresh_var(d), formb_id = elem::fresh_var(d);
			// Allocate interpreted and quoted arguments
			std::vector<elem> iparams, qparams, iargs, qargs;
			for(int_t a = 0; a < arity_num.num; a++) {
				iargs.push_back(elem::fresh_var(d));
				qargs.push_back(elem::fresh_var(d));
				iparams.push_back(elem::fresh_var(d));
				qparams.push_back(elem::fresh_var(d));
			}
			// Make the interpreters
			for(int_t a = 0; a < arity_num.num+1; a++) {
				// Make the head interpretation
				std::vector<elem> rhead_e = { out_rel, elem_openp, rule_name };
				for(int_t i = 0; i < a; i++) rhead_e.push_back(iparams[i]);
				rhead_e.push_back(elem_closep);
				// Make the rule quotation
				raw_term qrule({ quote_sym, elem_openp, elem(QRULE), elt_id,
					head_id, body_id, elem_closep });
				// Make the head quotation
				std::vector<elem> qhead_e = { quote_sym, elem_openp, elem(QTERM),
					head_id, rule_name };
				for(int_t i = 0; i < a; i++) qhead_e.push_back(qparams[i]);
				qhead_e.push_back(elem_closep);
				// Make the body interpretation
				std::vector<elem> body_e = { aux_rel, elem_openp, body_id };
				for(int_t i = 0; i < arity_num.num; i++) {
					body_e.push_back(qargs[i]);
					body_e.push_back(iargs[i]);
				}
				body_e.push_back(elem_closep);
				sprawformtree bodie =
					std::make_shared<raw_form_tree>(elem::AND,
						std::make_shared<raw_form_tree>(elem::AND,
							std::make_shared<raw_form_tree>(elem::NONE, qrule),
							std::make_shared<raw_form_tree>(elem::NONE, raw_term(qhead_e))),
						std::make_shared<raw_form_tree>(elem::NONE, raw_term(body_e)));
				// Fix the real parameters to this rule to the quoted symbol
				// if it is not marked as a variable.
				for(int_t i = 0; i < a; i++) {
					bodie = std::make_shared<raw_form_tree>(elem::AND, bodie,
						fix_symbols(quote_sym, qparams[i], iparams[i]));
				}
				// Fix the real parameters to this rule to be the same if their
				// quotations are the same.
				for(int_t i = 0; i < a; i++) {
					for(int_t j = i+1; j < a; j++) {
						bodie = std::make_shared<raw_form_tree>(elem::AND, bodie,
							fix_variables(quote_sym, qparams[i], iparams[i],
								qparams[j], iparams[j]));
					}
				}
				// Fix the real parameters to this rule to be the same as the
				// arguments if their corresponding quotations are the same.
				for(int_t i = 0; i < a; i++) {
					for(int_t j = 0; j < a; j++) {
						bodie = std::make_shared<raw_form_tree>(elem::AND, bodie,
							fix_variables(quote_sym, qargs[i], iargs[i], qparams[j],
								iparams[j]));
					}
				}
				raw_term rt(rhead_e);
				raw_rule rr(rt);
				rr.prft = bodie;
				rp.r.push_back(rr);
			}
			
			// Interpret terms of each arity
			for(int_t a = 0; a < arity_num.num+1; a++) {
				std::vector<elem> head = { aux_rel, elem_openp, elt_id };
				for(int_t i = 0; i < a; i++) {
					head.push_back(qparams[i]);
					head.push_back(iparams[i]);
				}
				for(int_t i = a; i < arity_num.num; i++) {
					head.push_back(und_sym);
					head.push_back(und_sym);
				}
				head.push_back(elem_closep);
				std::vector<elem> quote_e =
					{ quote_sym, elem_openp, elem(QTERM), elt_id, rule_name };
				for(int_t i = 0; i < a; i++) {
					quote_e.push_back(qparams[i]);
				}
				quote_e.push_back(elem_closep);
				std::vector<elem> real_e =
					{ out_rel, elem_openp, rule_name };
				for(int_t i = 0; i < a; i++) {
					real_e.push_back(iparams[i]);
				}
				real_e.push_back(elem_closep);
				sprawformtree bodie =
					std::make_shared<raw_form_tree>(elem::AND,
						std::make_shared<raw_form_tree>(elem::NONE, raw_term(quote_e)),
						std::make_shared<raw_form_tree>(elem::NONE, raw_term(real_e)));
				for(int_t i = 0; i < a; i++) {
					bodie = std::make_shared<raw_form_tree>(elem::AND, bodie,
						fix_symbols(quote_sym, qparams[i], iparams[i]));
				}
				for(int_t i = 0; i < a; i++) {
					for(int_t j = i+1; j < a; j++) {
						bodie = std::make_shared<raw_form_tree>(elem::AND, bodie,
							fix_variables(quote_sym, qparams[i], iparams[i],
								qparams[j], iparams[j]));
					}
				}
				raw_rule rr(head);
				rr.prft = bodie;
				rp.r.push_back(rr);
			}
			
			// Interpret equals
			if(arity_num.num >= 2) {
				std::vector<elem> head_e = { aux_rel, elem_openp, elt_id,
					qparams[0], iparams[0], qparams[1], iparams[1] };
				for(int_t i = 2; i < arity_num.num; i++) {
					head_e.push_back(und_sym);
					head_e.push_back(und_sym);
				}
				head_e.push_back(elem_closep);
				raw_term quote({quote_sym, elem_openp, elem(QEQUALS), elt_id,
					qparams[0], qparams[1], elem_closep});
				raw_term equals(raw_term::EQ, {iparams[0], elem_eq, iparams[1]});
				raw_rule rr(head_e);
				rr.prft = std::make_shared<raw_form_tree>(elem::AND,
					std::make_shared<raw_form_tree>(elem::AND,
						std::make_shared<raw_form_tree>(elem::NONE, quote),
						std::make_shared<raw_form_tree>(elem::NONE, equals)),
					std::make_shared<raw_form_tree>(elem::AND,
						fix_symbols(quote_sym, qparams[0], iparams[0]),
						fix_symbols(quote_sym, qparams[1], iparams[1])));
				rp.r.push_back(rr);
			}
			
			// Interpret not
			{
				std::vector<elem> head_e = { aux_rel, elem_openp, elt_id };
				for(int_t i = 0; i < arity_num.num; i++) {
					head_e.push_back(qparams[i]);
					head_e.push_back(iparams[i]);
				}
				head_e.push_back(elem_closep);
				raw_term quote({quote_sym, elem_openp, elem(QNOT), elt_id,
					forma_id, elem_closep });
				std::vector<elem> neg_e = { aux_rel, elem_openp, forma_id };
				for(int_t i = 0; i < arity_num.num; i++) {
					neg_e.push_back(qparams[i]);
					neg_e.push_back(iparams[i]);
				}
				neg_e.push_back(elem_closep);
				raw_rule rr(head_e);
				rr.prft = std::make_shared<raw_form_tree>(elem::AND,
					std::make_shared<raw_form_tree>(elem::NONE, quote),
					std::make_shared<raw_form_tree>(elem::NOT,
						std::make_shared<raw_form_tree>(elem::NONE, neg_e)));
				rp.r.push_back(rr);
			}
			
			// Interpret conjunctions
			generate_binary_eval(rp, QAND, elem::AND, quote_sym, und_sym,
				aux_rel, iparams, qparams);
			// Interpret disjunctions
			generate_binary_eval(rp, QALT, elem::ALT, quote_sym, und_sym,
				aux_rel, iparams, qparams);
			// Interpret implies
			generate_binary_eval(rp, QIMPLIES, elem::IMPLIES, quote_sym, und_sym,
				aux_rel, iparams, qparams);
			// Interpret coimplies
			generate_binary_eval(rp, QCOIMPLIES, elem::COIMPLIES, quote_sym, und_sym,
				aux_rel, iparams, qparams);
			
			// Interpret forall
			generate_quantified_eval(rp, QFORALL, elem::FORALL, quote_sym,
				aux_rel, iparams, qparams);
			// Interpret exists
			generate_quantified_eval(rp, QEXISTS, elem::EXISTS, quote_sym,
				aux_rel, iparams, qparams);
			// Interpret unique
			generate_quantified_eval(rp, QUNIQUE, elem::UNIQUE, quote_sym,
				aux_rel, iparams, qparams);
		}
	}
}

void driver::populate_free_variables(const raw_term &t,
		std::vector<elem> &bound_vars, std::set<elem> &free_vars) {
	for(const elem &e : t.e) {
		if(e.type == elem::VAR) {
			if(std::find(bound_vars.begin(), bound_vars.end(), e) ==
					bound_vars.end()) {
				free_vars.insert(e);
			}
		}
	}
}

void driver::populate_free_variables(const raw_form_tree &t,
		std::vector<elem> &bound_vars, std::set<elem> &free_vars) {
	switch(t.type) {
		case elem::IMPLIES:
			populate_free_variables(*t.l, bound_vars, free_vars);
			populate_free_variables(*t.r, bound_vars, free_vars);
			break;
		case elem::COIMPLIES:
			populate_free_variables(*t.l, bound_vars, free_vars);
			populate_free_variables(*t.r, bound_vars, free_vars);
			break;
		case elem::AND:
			populate_free_variables(*t.l, bound_vars, free_vars);
			populate_free_variables(*t.r, bound_vars, free_vars);
			break;
		case elem::ALT:
			populate_free_variables(*t.l, bound_vars, free_vars);
			populate_free_variables(*t.r, bound_vars, free_vars);
			break;
		case elem::NOT:
			populate_free_variables(*t.l, bound_vars, free_vars);
			break;
		case elem::EXISTS: {
			elem elt = *(t.l->el);
			bound_vars.push_back(elt);
			populate_free_variables(*t.r, bound_vars, free_vars);
			bound_vars.pop_back();
			break;
		} case elem::UNIQUE: {
			elem elt = *(t.l->el);
			bound_vars.push_back(elt);
			populate_free_variables(*t.r, bound_vars, free_vars);
			bound_vars.pop_back();
			break;
		} case elem::NONE: {
			populate_free_variables(*t.rt, bound_vars, free_vars);
			break;
		} case elem::FORALL: {
			elem elt = *(t.l->el);
			bound_vars.push_back(elt);
			populate_free_variables(*t.r, bound_vars, free_vars);
			bound_vars.pop_back();
			break;
		} default:
			assert(false); //should never reach here
	}
}

sprawformtree driver::with_exists(sprawformtree t,
		std::vector<elem> &bound_vars) {
	std::set<elem> free_vars;
	populate_free_variables(*t, bound_vars, free_vars);
	for(const elem &var : free_vars) {
		t = std::make_shared<raw_form_tree>(elem::EXISTS,
			std::make_shared<raw_form_tree>(elem::VAR, var), t);
	}
	return t;
}

void driver::insert_exists(raw_rule &rr) {
	if(rr.prft && rr.h.size() == 1) {
		std::vector<elem> bound_vars;
		for(const elem &e : rr.h[0].e) {
			if(e.type == elem::VAR) {
				bound_vars.push_back(e);
			}
		}
		rr.prft = with_exists(rr.prft, bound_vars);
	}
}

void driver::insert_exists(raw_prog &rp) {
	for(raw_rule &rr : rp.r) {
		insert_exists(rr);
	}
}

/* Reduce the size of the universe that the given variable takes its values from
 * by statically analyzing the term and determining what is impossible. */

void driver::reduce_universe(const elem &var, const raw_term &rt,
		std::set<elem> &universe, std::set<raw_term> &database) {
	if(rt.extype == raw_term::REL) {
		size_t var_pos;
		for(var_pos = 2; var_pos < rt.e.size() - 1 && rt.e[var_pos] != var; var_pos++);
		if(var_pos < rt.e.size() - 1) {
			std::set<elem> universe2;
			for(const raw_term &entry : database) {
				if(entry.e.size() == rt.e.size()) {
					size_t i;
					for(i = 0; i < entry.e.size(); i++) {
						if(rt.e[i].type != elem::VAR && rt.e[i] != entry.e[i]) {
							break;
						}
					}
					if(i == entry.e.size()) {
						universe2.insert(entry.e[var_pos]);
					}
				}
			}
			universe = universe2;
		}
	}
}

/* Reduce the size of the universe that the given variable takes its values from
 * by statically analyzing the logical formula and determining what is
 * impossible. */

void driver::reduce_universe(const elem &var, const raw_form_tree &t,
		std::set<elem> &universe, std::set<raw_term> &database) {
	switch(t.type) {
		case elem::IMPLIES: case elem::COIMPLIES: case elem::NOT:
			break;
		case elem::AND:
			reduce_universe(var, *t.l, universe, database);
			reduce_universe(var, *t.r, universe, database);
			break;
		case elem::ALT: {
			std::set<elem> universe2 = universe;
			reduce_universe(var, *t.l, universe2, database);
			reduce_universe(var, *t.r, universe, database);
			universe.insert(universe2.begin(), universe2.end());
			break;
		}	case elem::EXISTS: case elem::UNIQUE: case elem::FORALL: {
			const elem &qvar = *(t.l->el);
			if(qvar != var) {
				reduce_universe(var, *t.r, universe, database);
			}
			break;
		} case elem::NONE:
			reduce_universe(var, *t.rt, universe, database);
			break;
		default:
			assert(false); //should never reach here
	}
}

/* Reduce the size of the universe that the given variable takes its
 * values from by statically analyzing the rule and determining what is
 * impossible. */

void driver::reduce_universe(const elem &var, const raw_rule &rul,
		std::set<elem> &universe, std::set<raw_term> &database) {
	if(!rul.b.empty()) {
		std::set<elem> universe3;
		for(const std::vector<raw_term> &bodie : rul.b) {
			std::set<elem> universe2 = universe;
			for(const raw_term &rt : bodie) {
				reduce_universe(var, rt, universe2, database);
			}
			universe3.insert(universe2.begin(), universe2.end());
		}
		universe = universe3;
	} else if(rul.prft) {
		reduce_universe(var, *rul.prft, universe, database);
	}
}

/* Based on the current state of the database, use static analysis of
 * the logical formulas to remove from the universe of each quantification,
 * elements that could never satisfy their inner formula. */

void driver::populate_universes(const raw_form_tree &t,
		std::set<elem> &universe,
		std::map<const elem*, std::set<elem>> &universes,
		std::set<raw_term> &database) {
	switch(t.type) {
		case elem::IMPLIES:
			populate_universes(*t.l, universe, universes, database);
			populate_universes(*t.r, universe, universes, database);
			break;
		case elem::COIMPLIES:
			populate_universes(*t.l, universe, universes, database);
			populate_universes(*t.r, universe, universes, database);
			break;
		case elem::AND:
			populate_universes(*t.l, universe, universes, database);
			populate_universes(*t.r, universe, universes, database);
			break;
		case elem::ALT:
			populate_universes(*t.l, universe, universes, database);
			populate_universes(*t.r, universe, universes, database);
			break;
		case elem::NOT:
			populate_universes(*t.l, universe, universes, database);
			break;
		case elem::EXISTS: {
			populate_universes(*t.r, universe, universes, database);
			std::set<elem> universe2 = universe;
			const elem &elt = *(t.l->el);
			reduce_universe(elt, *t.r, universe2, database);
			universes[&elt] = universe2;
			break;
		} case elem::UNIQUE: {
			populate_universes(*t.r, universe, universes, database);
			std::set<elem> universe2 = universe;
			const elem &elt = *(t.l->el);
			reduce_universe(elt, *t.r, universe2, database);
			universes[&elt] = universe2;
			break;
		} case elem::NONE:
			break;
		case elem::FORALL: {
			populate_universes(*t.r, universe, universes, database);
			std::set<elem> universe2 = universe;
			const elem &elt = *(t.l->el);
			reduce_universe(elt, *t.r, universe2, database);
			universes[&elt] = universe2;
			break;
		} default:
			assert(false); //should never reach here
	}
}

/* Based on the current state of the database, use static analysis of
 * the logical formulas to remove from the universe of each quantification,
 * elements that could never satisfy their inner formula. */

void driver::populate_universes(const raw_rule &rul,
		std::set<elem> &universe,
		std::map<const elem*, std::set<elem>> &universes,
		std::set<raw_term> &database) {
	for(const raw_term &head : rul.h) {
		for(const elem &elt : head.e) {
			if(elt.type == elem::VAR) {
				std::set<elem> universe2 = universe;
				reduce_universe(elt, rul, universe2, database);
				universes[&elt] = universe2;
			}
		}
	}
	populate_universes(*rul.prft, universe, universes, database);
}

/* Evaluate the given logical term over the given database in the context
 * of the given bindings and return whether it is true or false. */

bool driver::evaluate_term(const raw_term &query, std::map<elem, elem> &bindings,
		std::set<raw_term> &database) {
	if(query.extype == raw_term::REL) {
		for(const raw_term &entry : database) {
			if(query.extype == raw_term::REL && query.e.size() == entry.e.size()) {
				bool succ = true;
				for(size_t i = 0; i < query.e.size(); i++) {
					if(!((query.e[i].type == elem::VAR && bindings[query.e[i]] == entry.e[i]) ||
							query.e[i] == entry.e[i])) {
						succ = false;
						break;
					} 
				}
				if(succ) return true;
			}
		}
	} else if(query.extype == raw_term::EQ) {
		elem lhs = query.e[0], rhs = query.e[2];
		if(lhs.type == elem::VAR) lhs = bindings[lhs];
		if(rhs.type == elem::VAR) rhs = bindings[rhs];
		return lhs == rhs;
	}
	return false;
}

/* Evaluate the given logical formula over the given database in the
 * context of the given bindings and return whether it is true or false.
 * The universes parameter is used to obtain the domain for each
 * quantification. */

bool driver::evaluate_form_tree(const raw_form_tree &t,
		const std::map<const elem*, std::set<elem>> &universes,
		std::map<elem, elem> &bindings, std::set<raw_term> &database) {
	switch(t.type) {
		case elem::IMPLIES:
			if(evaluate_form_tree(*t.l, universes, bindings, database)) {
				return evaluate_form_tree(*t.r, universes, bindings, database);
			} else {
				return true;
			}
		case elem::COIMPLIES:
			return evaluate_form_tree(*t.l, universes, bindings, database) ==
				evaluate_form_tree(*t.r, universes, bindings, database);
		case elem::AND:
			return evaluate_form_tree(*t.l, universes, bindings, database) &&
				evaluate_form_tree(*t.r, universes, bindings, database);
		case elem::ALT:
			return evaluate_form_tree(*t.l, universes, bindings, database) ||
				evaluate_form_tree(*t.r, universes, bindings, database);
		case elem::NOT:
			return !evaluate_form_tree(*t.l, universes, bindings, database);
		case elem::EXISTS: {
			const elem &var = *(t.l->el);
			std::optional<elem> prev_map = at_optional(bindings, var);
			for(const elem &elt : universes.at(&var)) {
				bindings[var] = elt;
				if(evaluate_form_tree(*t.r, universes, bindings, database)) {
					insert_optional(bindings, var, prev_map);
					return true;
				}
			}
			insert_optional(bindings, var, prev_map);
			return false;
		} case elem::UNIQUE: {
			size_t count = 0;
			const elem &var = *(t.l->el);
			std::optional<elem> prev_map = at_optional(bindings, var);
			for(const elem &elt : universes.at(&var)) {
				bindings[var] = elt;
				if(evaluate_form_tree(*t.r, universes, bindings, database)) {
					count++;
				}
			}
			insert_optional(bindings, var, prev_map);
			return count == 1;
		} case elem::NONE:
			return evaluate_term(*t.rt, bindings, database);
		case elem::FORALL: {
			const elem &var = *(t.l->el);
			std::optional<elem> prev_map = at_optional(bindings, var);
			for(const elem &elt : universes.at(&var)) {
				bindings[var] = elt;
				if(!evaluate_form_tree(*t.r, universes, bindings, database)) {
					insert_optional(bindings, var, prev_map);
					return false;
				}
			}
			insert_optional(bindings, var, prev_map);
			return true;
		} default:
			assert(false); //should never reach here
			return false;
	}
}

/* Interpret a rule. That is, run a rule over the current databaseand add the
 * discovered facts to the database. */

void driver::interpret_rule(size_t hd_idx, size_t inp_idx,
		const raw_rule &rul,
		const std::map<const elem*, std::set<elem>> &universes,
		std::map<elem, elem> &bindings, std::set<raw_term> &database) {
	const raw_term &head = rul.h[hd_idx];
	if(inp_idx < head.e.size() - 3) {
		if(head.e[inp_idx + 2].type == elem::VAR) {
			const elem &var = head.e[inp_idx + 2];
			for(const elem &elt : universes.at(&var)) {
				bindings[var] = elt;
				interpret_rule(hd_idx, inp_idx + 1, rul, universes, bindings, database);
			}
		} else {
			interpret_rule(hd_idx, inp_idx + 1, rul, universes, bindings, database);
		}
	} else {
		if(evaluate_form_tree(*rul.prft, universes, bindings, database)) {
			raw_term fact = head;
			for(elem &e : fact.e) {
				if(e.type == elem::VAR) {
					e = bindings[e];
				}
			}
			database.insert(fact);
		}
	}
}

void driver::populate_universe(const raw_term &rt,
		std::set<elem> &universe) {
	if(rt.extype == raw_term::REL) {
		for(size_t i = 2; i < rt.e.size() - 1; i++) {
			if(rt.e[i].type != elem::VAR) {
				universe.insert(rt.e[i]);
			}
		}
	} else if(rt.extype == raw_term::EQ) {
		if(rt.e[0].type != elem::VAR) {
			universe.insert(rt.e[0]);
		}
		if(rt.e[2].type != elem::VAR) {
			universe.insert(rt.e[2]);
		}
	}
}

void driver::populate_universe(const sprawformtree &t,
		std::set<elem> &universe) {
	switch(t->type) {
		case elem::IMPLIES:
			populate_universe(t->l, universe);
			populate_universe(t->r, universe);
			break;
		case elem::COIMPLIES:
			populate_universe(t->l, universe);
			populate_universe(t->r, universe);
			break;
		case elem::AND:
			populate_universe(t->l, universe);
			populate_universe(t->r, universe);
			break;
		case elem::ALT:
			populate_universe(t->l, universe);
			populate_universe(t->r, universe);
			break;
		case elem::NOT:
			populate_universe(t->l, universe);
			break;
		case elem::EXISTS: {
			populate_universe(t->r, universe);
			break;
		} case elem::UNIQUE: {
			populate_universe(t->r, universe);
			break;
		} case elem::NONE:
			populate_universe(*t->rt, universe);
			break;
		case elem::FORALL: {
			populate_universe(t->r, universe);
			break;
		} default:
			assert(false); //should never reach here
	}
}

void driver::populate_universe(const raw_prog &rp,
		std::set<elem> &universe) {
	for(const raw_rule &rr : rp.r) {
		for(const raw_term &rt : rr.h) {
			populate_universe(rt, universe);
		}
		populate_universe(rr.prft, universe);
	}
}

void driver::naive_pfp(const raw_prog &rp, std::set<elem> &universe,
		std::set<raw_term> &database) {
	populate_universe(rp, universe);
	std::set<raw_term> prev_database;
	// Interpret program
	do {
		prev_database = database;
		for(const raw_rule &rr : rp.r) {
			for(size_t hd_idx = 0; hd_idx < rr.h.size(); hd_idx++) {
				std::map<const elem*, std::set<elem>> universes;
				populate_universes(rr, universe, universes, database);
				std::map<elem, elem> bindings;
				interpret_rule(hd_idx, 0, rr, universes, bindings, database);
			}
		}
	} while(prev_database != database);
}

bool driver::transform(raw_progs& rp, size_t n, const strs_t& /*strtrees*/) {
	if (!rp.p.size()) return true;
	lexeme trel = { 0, 0 };
	directives_load(rp.p[n], trel);
	auto get_vars = [this](const raw_term& t) {
		for (const elem& e : t.e)
			if (e.type == elem::VAR)
				vars.insert(e.e);
	};
	auto get_all_vars = [get_vars](const raw_prog& p) {
		for (const raw_rule& r : p.r) {
			for (const raw_term& t : r.h) get_vars(t);
			for (const vector<raw_term>& b : r.b)
				for (const raw_term& t : b)
					get_vars(t);
		}
	};
	for (const raw_prog& p : rp.p) get_all_vars(p);
//	for (auto x : pd.strs)
//		if (!has(transformed_strings, x.first))
//			transform_string(x.second, rp.p[n], x.first),
//			transformed_strings.insert(x.first);
//	for (auto x : strtrees)
//		if (!has(transformed_strings, x.first))
//			transform_string(x.second, rp.p[n], x.first),
//			transformed_strings.insert(x.first);
	if (!rp.p[n].g.empty()) //{
		if (pd.strs.size() > 1)
			return throw_runtime_error(err_one_input);
//		else transform_grammar(rp.p[n], pd.strs.begin()->first,
//			pd.strs.begin()->second.size());
//	}
//	if (opts.enabled("sdt"))
//		for (raw_prog& p : rp.p)
//			p = transform_sdt(move(p));
	for (raw_prog& p : rp.p) {
		simplify_formulas(p);
		std::cout << "Simplified Program:" << std::endl << std::endl << p << std::endl;
		transform_quotes(p);
		std::cout << "Quoted Program:" << std::endl << std::endl << p << std::endl;
		transform_evals(p);
		std::cout << "Evaled Program:" << std::endl << std::endl << p << std::endl;
		insert_exists(p);
		std::cout << "Existentially Quantified Program:" << std::endl << std::endl << p << std::endl;
		cqc_strip(p);
		std::cout << "CQC Stripped Program:" << std::endl << std::endl << p << std::endl;
		std::set<elem> universe;
		std::set<raw_term> database;
		naive_pfp(p, universe, database);
		std::cout << "Fixed Point:" << std::endl << std::endl;
		for(const raw_term &entry : database) {
			std::cout << entry << "." << std::endl;
		}
		std::cout << std::endl << std::endl;
	}
#ifdef TRANSFORM_BIN_DRIVER
	if (opts.enabled("bin"))
		for (raw_prog& p : rp.p)
			transform_bin(p);
#endif
//	if (trel[0]) transform_proofs(rp.p[n], trel);
	//o::out()<<rp.p[n]<<endl;
//	if (pd.bwd) rp.p.push_back(transform_bwd(rp.p[n]));
	return true;
}

void driver::output_pl(const raw_prog& p) const {
	if (opts.enabled("xsb"))     print_xsb(o::to("xsb"), p);
	if (opts.enabled("swipl"))   print_swipl(o::to("swipl"), p);
	if (opts.enabled("souffle")) print_souffle(o::to("souffle"), p);
}

bool driver::prog_run(raw_progs& rp, size_t n, size_t steps,
	size_t break_on_step)
{
//	pd.clear();
	//DBG(o::out() << "original program:"<<endl<<p;)
//	strtrees.clear(), get_dict_stats(rp.p[n]), add_rules(rp.p[n]);
	clock_t start, end;
	size_t step = nsteps();
	measure_time_start();
	bool fp = tbl->run_prog(rp.p[n], pd.strs, steps, break_on_step);
	if (tbl->error) error = true;
	o::ms() << "# elapsed: ";
	measure_time_end();
	pd.elapsed_steps = nsteps() - step;
//	for (auto x : prog->strtrees_out)
//		strtrees.emplace(x.first, get_trees(prog->pd.strtrees[x.first],
//					x.second, prog->rng.bits));
	return fp;
}

bool driver::add(input* in) {
	if (!rp.parse(in, tbl->get_dict(), in->newseq)) return !(error = true);
	if (!in->newseq) transform(rp, pd.n, pd.strs);
	return true;
}

template <typename T>
void driver::list(std::basic_ostream<T>& os, size_t n) {
	size_t e = n ? n-- : rp.p.size();
	if (e > rp.p.size()) { os<<"# no such program exist"<<endl; return; }
	for (; n != e; ++n) os<<"# Listing program "<<(n + 1)<<":\n{\n"
		<<rp.p[n]<<"}\n";
	os << flush;
}
template void driver::list(std::basic_ostream<char>&, size_t);
template void driver::list(std::basic_ostream<wchar_t>&, size_t);

void driver::new_sequence() {
	//DBG(o::dbg() << "new sequence" << endl;)
	transform(rp, pd.n, pd.strs);
	raw_prog &p = rp.p[pd.n];
	for (const string& s : str_bltins) p.builtins.insert(get_lexeme(s));
	output_pl(p);
}

void driver::restart() {
	pd.n = 0;
	pd.start_step = nsteps();
	running = true;
}

bool driver::run(size_t steps, size_t break_on_step, bool break_on_fp) {
	if (!rp.p.size()) return result = true;
	if (!running) restart();
next_sequence:
	if (nsteps() == pd.start_step) new_sequence();
	if (opts.disabled("run") && opts.disabled("repl"))
		return true;
	bool fp = prog_run(rp, pd.n, steps, break_on_step);
	if (fp) {
		//DBG(if (opts.enabled("dump")) out(o::dump());)
		if (pd.n == rp.p.size()-1) // all progs fp
			return result = true, true;
		++pd.n;
		pd.start_step = nsteps();
		if (steps && steps >= pd.elapsed_steps)
			if (!(steps -= pd.elapsed_steps)) return false;
		if ((break_on_step && nsteps() == break_on_step)
			|| break_on_fp) return false;
		goto next_sequence;
	}
	return false;
}

bool driver::step(size_t steps, size_t break_on_step, bool break_on_fp) {
	return run(steps, break_on_step, break_on_fp);
}

template <typename T>
void driver::info(std::basic_ostream<T>& os) {
	size_t l = rp.p.size();
	os<<"# prog n:    \t" << (pd.n+1) <<" of: " << (l>0?l:0) << endl;
	os<<"# step:      \t" << nsteps() <<" - " << pd.start_step <<" = "
		<< (nsteps() - pd.start_step) << " ("
		<< (running ? "" : "not ") << "running)" << endl;
	bdd::stats(os<<"# bdds:     \t")<<endl;
	//DBG(os<<"# opts:    \t" << opts << endl;)
}
template void driver::info(std::basic_ostream<char>&);
template void driver::info(std::basic_ostream<wchar_t>&);

size_t driver::size() {
	return archive::size(*this);
}

void driver::db_load(std::string filename) {
	load_archives.emplace_back(archive::type::BDD, filename, 0, false);
	load_archives.back() >> *this;
}

void driver::db_save(std::string filename) {
	archive ar(archive::type::BDD, filename, archive::size(*this), true);
	ar << *this;
}

void driver::load(std::string filename) {
	if (!ii->size()) {
		load_archives.emplace_back(archive::type::DRIVER, filename,0,0);
		if (!load_archives.back().error) load_archives.back() >> *this;
		return;
	}
	error = true;
	throw_runtime_error(
		"Loading into a running program is not yet supported."); // TODO
}

void driver::save(std::string filename) {
	archive ar(archive::type::DRIVER, filename, archive::size(*this), true);
	ar << *this;
}

void driver::read_inputs() {
	//COUT << "read_inputs() current_input: " << current_input << " next_input: " << (current_input ? current_input->next() : 0) << endl;
	while (current_input && current_input->next()) {
		current_input = current_input->next();
		if (!add(current_input)) return;
		++current_input_id;
		//COUT << "current_inputid: " << current_input_id << endl;
	}
}

driver::driver(string s, const options &o) : rp(), opts(o) {
	dict_t dict;

	// inject inputs from opts to driver and dict (needed for archiving)
	dict.set_inputs(ii = opts.get_inputs());

	if (s.size()) opts.parse(strings{ "-ie", s });

	// we don't need the dict any more, tables owns it from now on...
	tbl = new tables(move(dict), opts.enabled("proof"), 
		opts.enabled("optimize"), opts.enabled("bin"),
		opts.enabled("t"), opts.enabled("regex"));
	set_print_step(opts.enabled("ps"));
	set_print_updates(opts.enabled("pu"));
	set_populate_tml_update(opts.enabled("tml_update"));
	if (!ii) return;
	current_input = ii->first();
	if (current_input && !add(current_input)) return;
	read_inputs();
}

driver::driver(FILE *f, const options &o) : driver(input::file_read_text(f),o){}
driver::driver(string_t s, const options& o)	: driver(to_string(s), o) {}
driver::driver(const char *s, const options &o)	: driver(string(s), o) {}
driver::driver(ccs   s, const options &o)	: driver(string_t(s), o) {}
driver::driver(const options &o)	: driver(string(), o) {}
driver::driver(string s)		: driver(s, options()) {}
driver::driver(FILE *f)			: driver(f, options()) {}
driver::driver(string_t s)		: driver(to_string(s)) {}
driver::driver(const char *s)		: driver(s, options()) {}
driver::driver(ccs   s)			: driver(string_t(s)) {}

driver::~driver() {
	if (tbl) delete tbl;
	for (auto x : strs_allocated) free((char *)x);
}
