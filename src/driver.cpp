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

/* Takes a raw term and its position in the program to be quoted and returns
 * its quotation within a relation of the given name. The locations of variable
 * elements within the raw term are added to the variables vector. */

raw_term driver::quote_term(const raw_term &head, const elem &rel_name, int_t rule_idx, int_t disjunct_idx, int_t goal_idx, std::vector<quote_coord> &variables) {
	// The elements of the term that we're building up
	std::vector<elem> quoted_term_e;
	// Add metadata to quoted term: term signature, rule #, disjunct #, goal #, total inputs, relation sym
	quoted_term_e.insert(quoted_term_e.end(),
		{rel_name, elem_openp, elem(0), uelem(rule_idx), uelem(disjunct_idx), uelem(goal_idx), uelem(ssize(head.e)-3), head.e[0] });
	for(int_t param_idx = 2; param_idx < ssize(head.e) - 1; param_idx ++) {
		if(head.e[param_idx].type == elem::VAR) {
			// Convert the variable to a symbol and add it to quouted term
			elem var_sym_elem(elem::SYM, head.e[param_idx].e);
			quoted_term_e.push_back(var_sym_elem);
			// Log the fact that a variable occurs at this location
			variables.push_back({rule_idx, disjunct_idx, goal_idx, param_idx-2});
		} else {
			quoted_term_e.push_back(head.e[param_idx]);
		}
	}
	// Terminate term elements and make raw_term object
	quoted_term_e.push_back(elem_closep);
	return raw_term(quoted_term_e);
}

/* Parse an STR elem into a raw_prog. */

raw_prog driver::read_prog(elem prog, const raw_prog &rp) {
	lexeme prog_str = {prog.e[0]+1, prog.e[1]-1};
	input *prog_in = dynii.add_string(lexeme2str(prog_str));
	prog_in->prog_lex();
	raw_prog nrp;
	nrp.builtins = rp.builtins;
	nrp.parse(prog_in, tbl->get_dict());
	return nrp;
}

/* Loop through the rules of the given program checking if they use a function
 * called "quote" in their bodies. Quote's first argument is the relation into
 * which it should put the quotation it creates, and it's second argument is the
 * rule to quote. Say that the output relation name is s, quote will populate it
 * according to the following schema:
 * For each context, each N-ary term is stored as:
 * s(0 <rule #> <disjunct #> <goal #> <total inputs> <relname> <input0> <input1> ... <inputN>)
 * The locations of the variables in the above schema are stored as:
 * s(1 <rule #> <disjunct #> <goal #> <input #>) */

void driver::transform_quotes(raw_prog &rp) {
	for(raw_rule &outer_rule : rp.r) {
		// Iterate through the bodies of the current rule looking for uses of the
		// "quote" relation.
		for(raw_term &rhs_term : outer_rule.h) {
			// Search for uses of quote within a relation.
			for(int_t offset = 3; offset < ssize(rhs_term.e); offset ++) {
				if(rhs_term.e[offset].type == elem::STR && rhs_term.e[offset].e[1] > rhs_term.e[offset].e[0] && *rhs_term.e[offset].e[0] == '`') {
					raw_prog nrp = read_prog(rhs_term.e[offset], rp);
					// The relation under which the quotation we build will be stored.
					elem rel_name = rhs_term.e[offset - 1];
					// Replace the whole quotation with the relation it will create.
					rhs_term.e.erase(rhs_term.e.begin() + offset);
					rhs_term.calc_arity(nullptr);
					// Maintain a list of locations where variables occur:
					std::vector<quote_coord> variables;
					for(int_t ridx = 0; ridx < ssize(nrp.r); ridx++) {
						for(int_t didx = 0; didx < ssize(nrp.r[ridx].b) + 1; didx++) {
							const std::vector<raw_term> &bodie = didx == 0 ? nrp.r[ridx].h : nrp.r[ridx].b[didx-1];
							for(int_t gidx = 0; gidx < ssize(bodie); gidx++) {
								rp.r.push_back(raw_rule(quote_term(bodie[gidx], rel_name, ridx, didx, gidx, variables)));
							}
						}
					}
					
					// Now create sub-relation to store the location of variables in the quoted relation
					for(auto const& [rule_idx, disjunct_idx, goal_idx, arg_idx] : variables) {
						rp.r.push_back(raw_rule(raw_term({ rel_name, elem_openp, elem(1), uelem(rule_idx), uelem(disjunct_idx), uelem(goal_idx), uelem(arg_idx), elem_closep })));
					}
				}
			}
		}
	}
}

/* Generate a unique variable and update the counter. */

elem driver::generate_var(int &var_counter) {
	input *i = dynii.add_string("?" + std::to_string(var_counter++));
	i->prog_lex();
	elem var;
	var.parse(i);
	return var;
}

/* Extract the arities stored in a quote arity relation. A quote arity relation
 * has the following schema:
 * s(0 <rule #> <disjunct #> <goal #> <total inputs> ...)
 * Note that this means that every quote relation contains a quote arity relation. */

std::vector<quote_coord> driver::extract_quote_arity(const elem &quote_rel, const raw_prog &rp) {
	std::vector<quote_coord> quote_shape;
	for(const raw_rule &rr : rp.r) {
		if(lexeme2str(rr.h[0].e[0].e) == lexeme2str(quote_rel.e) && rr.h[0].e[2].num == 0) {
			quote_shape.push_back({ rr.h[0].e[3].num, rr.h[0].e[4].num, rr.h[0].e[5].num, rr.h[0].e[6].num });
		}
	}
	return quote_shape;
}

/* Extract the arities stored in a quote arity relation and put them into a tree
 * format. */

program_arity driver::extract_quote_arity_tree(const elem &quote_rel, const raw_prog &rp) {
	std::vector<quote_coord> prog_shape = extract_quote_arity(quote_rel, rp);
	program_arity prog_tree;
	// We need the verticies to be in lexicographic order for the loop to
	// reconstruct the tree correctly.
	std::sort(prog_shape.begin(), prog_shape.end());
	quote_coord prev_pos { -1, 0, 0, 0 };
	// Put the program arity into the form of a tree.
	for(auto const& pos : prog_shape) {
		// Figure out which rule and where in the rule to put this term.
		if(pos[0] != prev_pos[0]) {
			// Case where we have encountered new rule in map
			prog_tree.push_back({{pos[3]}});
		} else if(pos[1] != prev_pos[1]) {
			// Case where we have encountered new disjunct in map
			prog_tree.back().push_back({pos[3]});
		} else if(pos[2] != prev_pos[2]) {
			// Case where we have encountered new goal in map
			prog_tree.back().back().push_back(pos[3]);
		}
		prev_pos = pos;
	}
	return prog_tree;
}

/* Loop through the rules of the given program checking if they use a relation
 * called "eval" in their bodies. If eval is used, take its single argument,
 * the name of a relation containing a representation of a TML program, and
 * append to the current program a relation equivalent to the original TML
 * program but that only depends on the relation's arity and its name - not
 * its entries. */

void driver::transform_evals(raw_prog &rp) {
	for(const raw_rule &outer_rule : rp.r) {
		// Iterate through the bodies of the current rule looking for uses of the
		// "eval" relation.
		for(const raw_term &rhs_term : outer_rule.h) {
			if(rhs_term.e[0].type == elem::SYM && to_string_t("eval") == lexeme2str(rhs_term.e[0].e)) {
				// The first parenthesis marks the beginning of eval's three arguments.
				if(ssize(rhs_term.e) == 6 && rhs_term.e[1].type == elem::OPENP && rhs_term.e[5].type == elem::CLOSEP) {
					// The relation to contain the evaled relation is the first symbol between the parentheses
					elem out_rel = rhs_term.e[2];
					// The relation containing the quotation arity is the second symbol between the parentheses
					elem arity_rel = rhs_term.e[3];
					// The formal symbol representing the quotation relation is the third symbol between the parentheses
					elem quote_sym = rhs_term.e[4];
					// Get the program arity in tree form
					program_arity prog_tree = extract_quote_arity_tree(arity_rel, rp);
					
					// We want to generate a lot of unique variables. We do this by maintaining
					// a counter. At any point in time, its string representation will be the
					// name of the next generated variable.
					int var_counter = 1;
					
					for(int_t ridx = 0; ridx < ssize(prog_tree); ridx++) {
						for(int_t hidx = 0; hidx < ssize(prog_tree[ridx][0]); hidx++) {
							// Exclusively store the variables that we have created in the
							// following two maps.
							std::map<quote_coord, elem> quote_map;
							std::map<quote_coord, elem> real_map;
							
							// 1) Make the eval rule head. First input is the name of the
							// rule. Needed because the quoted program most likely contains
							// multiple rules. The rest of the inputs are the values that
							// would be supplied to the rule in the quoted program. I.e.
							// these are not meta.
							std::vector<elem> head_elems = { out_rel, elem_openp, real_map[{ridx, 0, hidx, -1}] = generate_var(var_counter) };
							for(int_t inidx = 0; inidx < prog_tree[ridx][0][hidx]; inidx++) {
								head_elems.push_back(real_map[{ridx, 0, hidx, inidx}] = generate_var(var_counter));
							}
							head_elems.push_back(elem_closep);
							raw_term head(head_elems);
							
							// Start of with the true constant (0=0), and add conjunctions
							raw_form_tree *body_tree = new raw_form_tree(elem::NONE, raw_term(raw_term::EQ, {elem(0), elem_eq, elem(0)}));
							
							// 2) Make the quoted term declaration section. These variables
							// take on the parameter names and relation names of the quoted
							// program. I.e. these are meta, describing the program as a
							// formal object.
							for(int_t didx = 0; didx < ssize(prog_tree[ridx]); didx++) {
								for(int_t gidx = 0; gidx < ssize(prog_tree[ridx][didx]); gidx++) {
									if(didx == 0 && gidx != hidx) continue;
									std::vector<elem> a = { quote_sym, elem_openp, elem(0), uelem(ridx), uelem(didx), uelem(gidx), uelem(prog_tree[ridx][didx][gidx]),
										quote_map[{ridx, didx, gidx, -1}] = (didx == 0 ? real_map[{ridx, 0, hidx, -1}] : generate_var(var_counter)) };
									for(int_t inidx = 0; inidx < prog_tree[ridx][didx][gidx]; inidx++) {
										a.push_back(quote_map[{ridx, didx, gidx, inidx}] = generate_var(var_counter));
									}
									a.push_back(elem_closep);
									body_tree = new raw_form_tree(elem::AND, body_tree, new raw_form_tree(elem::NONE, raw_term(a)));
								}
							}
							// 3) Make the real term declaration section. These variables
							// take on the same values that the inputs to the quoted program
							// would. I.e. this is not meta. Since the head is at the head,
							// we just do the body
							for(int_t didx = 1; didx < ssize(prog_tree[ridx]); didx++) {
								for(int_t gidx = 0; gidx < ssize(prog_tree[ridx][didx]); gidx++) {
									std::vector<elem> a = { out_rel, elem_openp, real_map[{ridx, didx, gidx, -1}] = quote_map[{ridx, didx, gidx, -1}] };
									for(int_t inidx = 0; inidx < prog_tree[ridx][didx][gidx]; inidx++) {
										a.push_back(real_map[{ridx, didx, gidx, inidx}] = generate_var(var_counter));
									}
									a.push_back(elem_closep);
									body_tree = new raw_form_tree(elem::AND, body_tree, new raw_form_tree(elem::NONE, raw_term(a)));
								}
							}
							// 4) Make the variable sameness section. These propositions
							// ensure that is two quoted inputs labelled as variables are
							// the same, then their corresponding real inputs are
							// constrained to be same.
							for(int_t didx1 = 0; didx1 < ssize(prog_tree[ridx]); didx1++) {
								for(int_t gidx1 = 0; gidx1 < ssize(prog_tree[ridx][didx1]); gidx1++) {
									if(didx1 == 0 && gidx1 != hidx) continue;
									for(int_t inidx1 = 0; inidx1 < prog_tree[ridx][didx1][gidx1]; inidx1++) {
										for(int_t didx2 = didx1; didx2 < ssize(prog_tree[ridx]); didx2++) {
											for(int_t gidx2 = 0; gidx2 < ssize(prog_tree[ridx][didx2]); gidx2++) {
												if(didx2 == 0 && gidx2 != hidx) continue;
												for(int_t inidx2 = 0; inidx2 < prog_tree[ridx][didx2][gidx2]; inidx2++) {
													// Without this, each formula would be constructed twice.
													if(std::make_tuple(didx1, gidx1, inidx1) >= std::make_tuple(didx2, gidx2, inidx2)) continue;
													raw_term a({ quote_sym, elem_openp, elem(1), uelem(ridx), uelem(didx1), uelem(gidx1), uelem(inidx1), elem_closep }),
														b({ quote_sym, elem_openp, elem(1), uelem(ridx), uelem(didx2), uelem(gidx2), uelem(inidx2), elem_closep }),
														c(raw_term::EQ, { quote_map[{ridx, didx1, gidx1, inidx1}], elem_eq, quote_map[{ridx, didx2, gidx2, inidx2}] }),
														d(raw_term::EQ, { real_map[{ridx, didx1, gidx1, inidx1}], elem_eq, real_map[{ridx, didx2, gidx2, inidx2}] });
													body_tree = new raw_form_tree(elem::AND, body_tree,
														new raw_form_tree(elem::IMPLIES,
															new raw_form_tree(elem::AND,
																new raw_form_tree(elem::AND,
																	new raw_form_tree(elem::NONE, a),
																	new raw_form_tree(elem::NONE, b)),
																new raw_form_tree(elem::NONE, c)),
																new raw_form_tree(elem::NONE, d)));
												}
											}
										}
									}
								}
							}
							// 5) Make the symbol fixing section. Essentially, some of the
							// inputs to rules in the quoted program will be literal symbols
							// rather than variables. If this is the case, then fix the
							// literals into the evaled program relation.
							for(int_t didx = 0; didx < ssize(prog_tree[ridx]); didx++) {
								for(int_t gidx = 0; gidx < ssize(prog_tree[ridx][didx]); gidx++) {
									if(didx == 0 && gidx != hidx) continue;
									for(int_t inidx = 0; inidx < prog_tree[ridx][didx][gidx]; inidx++) {
										raw_term a({ quote_sym, elem_openp, elem(1), uelem(ridx), elem(0), uelem(hidx), uelem(inidx), elem_closep });
										raw_term b(raw_term::EQ, { quote_map[{ridx, didx, gidx, inidx}], elem_eq, real_map[{ridx, didx, gidx, inidx}] });
										body_tree = new raw_form_tree(elem::AND, body_tree,
											new raw_form_tree(elem::IMPLIES,
												new raw_form_tree(elem::NOT, new raw_form_tree(elem::NONE, a)),
												new raw_form_tree(elem::NONE, b)));
									}
								}
							}
							// 6) Existentially quantify all the variables being used in
							// the body. This should not be necessary (going by syntax/
							// semantics of other relational calculus languages), but just
							// in case.
							for(auto const& [pos, var] : quote_map) {
								if(!(pos[1] == 0 && pos[3] == -1)) {
									body_tree = new raw_form_tree(elem::EXISTS, new raw_form_tree(elem::VAR, var), body_tree);
								}
							}
							for(auto const& [pos, var] : real_map) {
								// Only quantify variable if it is not in the head of the rule
								if(pos[1] != 0) {
									body_tree = new raw_form_tree(elem::EXISTS, new raw_form_tree(elem::VAR, var), body_tree);
								}
							}
							
							// 7) Put the body and head constructed above together to make a
							// rule and add that to the program.
							raw_rule rr;
							rr.h.push_back(head);
							rr.prft = std::shared_ptr<raw_form_tree>(body_tree);
							rp.r.push_back(rr);
						}
					}
				}
			}
		}
	}
}

/* Reduce the size of the universe that the given variable takes its values from
 * by statically analyzing the term and determining what is impossible. */

void driver::reduce_universe(const elem &var, const raw_term &rt, std::set<elem> &universe, std::set<raw_term> &database) {
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

void driver::reduce_universe(const elem &var, const raw_form_tree &t, std::set<elem> &universe, std::set<raw_term> &database) {
	switch(t.type) {
		case elem::IMPLIES:
			break;
		case elem::COIMPLIES:
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
		} case elem::NOT:
			break;
		case elem::EXISTS:
			reduce_universe(var, *t.r, universe, database);
			break;
		case elem::UNIQUE:
			reduce_universe(var, *t.r, universe, database);
			break;
		case elem::NONE:
			reduce_universe(var, *t.rt, universe, database);
			break;
		case elem::FORALL:
			reduce_universe(var, *t.r, universe, database);
			break;
		default:
			assert(false); //should never reach here
	}
}

/* Reduce the size of the universe that the given variable takes its values from
 * by statically analyzing the rule and determining what is impossible. */

void driver::reduce_universe(const elem &var, const raw_rule &rul, std::set<elem> &universe, std::set<raw_term> &database) {
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

/* Based on the current state of the database, use static analysis of the
 * logical formulas to remove from the universe of each quantification, elements
 * that could never satisfy their inner formula. */

void driver::populate_universes(const raw_form_tree &t, std::set<elem> &universe, std::map<elem, std::set<elem>> &universes, std::set<raw_term> &database) {
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
			elem elt = *(t.l->el);
			reduce_universe(elt, *t.r, universe2, database);
			universes[elt] = universe2;
			break;
		} case elem::UNIQUE: {
			populate_universes(*t.r, universe, universes, database);
			std::set<elem> universe2 = universe;
			elem elt = *(t.l->el);
			reduce_universe(elt, *t.r, universe2, database);
			universes[elt] = universe2;
			break;
		} case elem::NONE:
			break;
		case elem::FORALL: {
			populate_universes(*t.r, universe, universes, database);
			std::set<elem> universe2 = universe;
			elem elt = *(t.l->el);
			reduce_universe(elt, *t.r, universe2, database);
			universes[elt] = universe2;
			break;
		} default:
			assert(false); //should never reach here
	}
}

/* Based on the current state of the database, use static analysis of the
 * logical formulas to remove from the universe of each quantification, elements
 * that could never satisfy their inner formula. */

void driver::populate_universes(const raw_rule &rul, std::set<elem> &universe, std::map<elem, std::set<elem>> &universes, std::set<raw_term> &database) {
	for(const raw_term &head : rul.h) {
		for(const elem &elt : head.e) {
			if(elt.type == elem::VAR) {
				std::set<elem> universe2 = universe;
				reduce_universe(elt, rul, universe2, database);
				universes[elt] = universe2;
			}
		}
	}
	if(rul.b.empty() && rul.prft) {
		populate_universes(*rul.prft, universe, universes, database);
	}
}

/* Evaluate the given logical term over the given database in the context of
 * the given bindings and return whether it is true or false. */

bool driver::evaluate_term(const raw_term &query, std::map<elem, elem> &bindings, std::set<raw_term> &database) {
	if(query.extype == raw_term::REL) {
		for(const raw_term &entry : database) {
			if(query.extype == raw_term::REL && query.e.size() == entry.e.size()) {
				bool succ = true;
				for(size_t i = 0; i < query.e.size(); i++) {
					if(!((query.e[i].type == elem::VAR && bindings[query.e[i]] == entry.e[i]) || query.e[i] == entry.e[i])) {
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

/* Evaluate the given logical formula over the given database in the context of
 * the given bindings and return whether it is true or false. The universes
 * parameter is used to obtain the domain for each quantification. */

bool driver::evaluate_form_tree(const raw_form_tree &t, const std::map<elem, std::set<elem>> &universes, std::map<elem, elem> &bindings, std::set<raw_term> &database) {
	switch(t.type) {
		case elem::IMPLIES:
			if(evaluate_form_tree(*t.l, universes, bindings, database)) {
				return evaluate_form_tree(*t.r, universes, bindings, database);
			} else {
				return true;
			}
		case elem::COIMPLIES:
			return evaluate_form_tree(*t.l, universes, bindings, database) == evaluate_form_tree(*t.r, universes, bindings, database);
		case elem::AND:
			return evaluate_form_tree(*t.l, universes, bindings, database) && evaluate_form_tree(*t.r, universes, bindings, database);
		case elem::ALT:
			return evaluate_form_tree(*t.l, universes, bindings, database) || evaluate_form_tree(*t.r, universes, bindings, database);
		case elem::NOT:
			return !evaluate_form_tree(*t.l, universes, bindings, database);
		case elem::EXISTS: {
			const elem &var = *(t.l->el);
			for(const elem &elt : universes.at(var)) {
				bindings[var] = elt;
				if(evaluate_form_tree(*t.r, universes, bindings, database)) {
					return true;
				}
			}
			return false;
		} case elem::UNIQUE: {
			size_t count = 0;
			const elem &var = *(t.l->el);
			for(const elem &elt : universes.at(var)) {
				bindings[var] = elt;
				if(evaluate_form_tree(*t.r, universes, bindings, database)) {
					count++;
				}
			}
			return count == 1;
		} case elem::NONE:
			return evaluate_term(*t.rt, bindings, database);
		case elem::FORALL: {
			const elem &var = *(t.l->el);
			for(const elem &elt : universes.at(var)) {
				bindings[var] = elt;
				if(!evaluate_form_tree(*t.r, universes, bindings, database)) {
					return false;
				}
			}
			return true;
		} default:
			assert(false); //should never reach here
			return false;
	}
}

/* Interpret a rule. That is, run a rule over the current databaseand add the
 * discovered facts to the database. */

void driver::interpret_rule(size_t hd_idx, size_t inp_idx, const raw_rule &rul, const std::map<elem, std::set<elem>> &universes, std::map<elem, elem> &bindings, std::set<raw_term> &database) {
	const raw_term &head = rul.h[hd_idx];
	if(inp_idx < head.e.size() - 3) {
		if(head.e[inp_idx + 2].type == elem::VAR) {
			const elem &var = head.e[inp_idx + 2];
			for(const elem &elt : universes.at(var)) {
				bindings[var] = elt;
				interpret_rule(hd_idx, inp_idx + 1, rul, universes, bindings, database);
			}
		} else {
			interpret_rule(hd_idx, inp_idx + 1, rul, universes, bindings, database);
		}
	} else {
		bool succ;
		if(!rul.b.empty()) {
			succ = false;
			for(const std::vector<raw_term> &bodie : rul.b) {
				bool and_succ = true;
				for(const raw_term &rt : bodie) {
					and_succ &= evaluate_term(rt, bindings, database);
				}
				succ |= and_succ;
			}
		} else if(rul.prft) {
			succ = evaluate_form_tree(*rul.prft, universes, bindings, database);
		} else {
			succ = true;
		}
		if(succ) {
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

void driver::naive_pfp(const raw_prog &rp, std::set<elem> &universe, std::set<raw_term> &database) {
	// Populate our universe
	for(const raw_rule &rr : rp.r) {
		for(const raw_term &rt : rr.h) {
			for(size_t i = 2; i < rt.e.size() - 1; i++) {
				if(rt.e[i].type != elem::VAR) {
					universe.insert(rt.e[i]);
				}
			}
		}
		for(const std::vector<raw_term> &bodie : rr.b) {
			for(const raw_term &rt : bodie) {
				for(size_t i = 2; i < rt.e.size() - 1; i++) {
					if(rt.e[i].type != elem::VAR) {
						universe.insert(rt.e[i]);
					}
				}
			}
		}
	}
	
	std::set<raw_term> prev_database;
	// Interpret program
	do {
		prev_database = database;
		for(const raw_rule &rr : rp.r) {
			for(size_t hd_idx = 0; hd_idx < rr.h.size(); hd_idx++) {
				std::map<elem, std::set<elem>> universes;
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
		transform_quotes(p);
		std::cout << "Quoted Program:" << std::endl << std::endl << p << std::endl;
		transform_evals(p);
		std::cout << "Evaled Program:" << std::endl << std::endl << p << std::endl;
		std::set<elem> universe;
		std::set<raw_term> database;
		naive_pfp(p, universe, database);
		std::cout << "Fixed Point:" << std::endl << std::endl;
		for(const raw_term &entry : database) {
			std::cout << entry << std::endl;
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
	if (!rp.parse(in, tbl->get_dict(), in->newseq)) return error=true,false;
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

driver::driver(string s, options o) : rp(), opts(o) {
	dict_t dict;

	// inject inputs from opts to driver and dict (needed for archiving)
	dict.set_inputs(ii = opts.get_inputs());

	if (s.size()) opts.parse(strings{ "-ie", s });

	// we don't need the dict any more, tables owns it from now on...
	tbl = new tables(move(dict), opts.enabled("proof"), 
		opts.enabled("optimize"), opts.enabled("bin"),
		opts.enabled("t"));
	set_print_step(opts.enabled("ps"));
	set_print_updates(opts.enabled("pu"));
	set_populate_tml_update(opts.enabled("tml_update"));
	if (ii) {
		current_input = ii->first();
		if (current_input)
			if (!add(current_input)) return;
		read_inputs();
	}
}
driver::driver(FILE *f,    options o)   : driver(input::file_read_text(f), o) {}
driver::driver(string_t s, options o)   : driver(to_string(s), o) {}
driver::driver(const char *s,options o) : driver(string(s), o) {}
driver::driver(ccs   s,    options o)   : driver(string_t(s), o) {}
driver::driver(options o)               : driver(string(), o) {}
driver::driver(string s)                : driver(s, options()) {}
driver::driver(FILE *f)                 : driver(f, options()) {}
driver::driver(string_t s)              : driver(to_string(s)) {}
driver::driver(const char *s)           : driver(s, options()) {}
driver::driver(ccs   s)                 : driver(string_t(s)) {}

driver::~driver() {
	if (tbl) delete tbl;
	for (auto x : strs_allocated) free((char *)x);
}
