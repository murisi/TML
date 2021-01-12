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
		sprawformtree tmp = rr.get_prft();
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

/* Puts the formulas parented by a tree of associative binary operators
 * into a flat list. */

void driver::flatten_associative(const elem::etype &tp,
		const sprawformtree &tree, std::vector<sprawformtree> &tms) {
	if(tree->type == tp) {
		flatten_associative(tp, tree->l, tms);
		flatten_associative(tp, tree->r, tms);
	} else {
		tms.push_back(tree);
	}
}

/* Checks if the body of the given rule is conjunctive. */

bool driver::is_cq(const raw_rule &rr) {
	// Ensure that there are no disjunctions
	if(rr.h.size() != 1 || rr.b.size() != 1) return false;
	// Ensure that head is positive
	if(rr.h[0].neg) return false;
	// Ensure that each body term is positive and is a relation
	for(const raw_term &rt : rr.b[0]) {
		if(rt.neg || rt.extype != raw_term::REL) return false;
	}
	return true;
}

/* Checks if the body of the given rule is conjunctive with negation. */

bool driver::is_cqn(const raw_rule &rr) {
	// Ensure that there are no disjunctions
	if(rr.h.size() != 1 || rr.b.size() != 1) return false;
	// Ensure that head is positive
	if(rr.h[0].neg) return false;
	// Ensure that each body term is a relation
	for(const raw_term &rt : rr.b[0]) {
		if(rt.extype != raw_term::REL) return false;
	}
	return true;
}

/* Convenience function for getting relation name and arity from
 * term. */

rel_info get_relation_info(const raw_term &rt) {
	return std::make_tuple(rt.e[0], rt.e.size() - 3);
}

/* If rr1 and rr2 are both conjunctive queries, check if there is a
 * homomorphism rr2 to rr1. By the homomorphism theorem, the existence
 * of a homomorphism implies that rr1 is contained by rr2. */

bool driver::cqc(const raw_rule &rr1, const raw_rule &rr2) {
	// Get dictionary for generating fresh symbols
	dict_t &old_dict = tbl->get_dict();
	dict_t d;
	d.op = old_dict.op;
	d.cl = old_dict.cl;
	
	if(is_cq(rr1) && is_cq(rr2) &&
			get_relation_info(rr1.h[0]) == get_relation_info(rr2.h[0])) {
		// Freeze the variables and symbols of the rule we are checking the
		// containment of
		std::map<elem, elem> freeze_map;
		raw_rule frozen_rr1 = freeze_rule(rr1, freeze_map, d);
		
		// Build up the queries necessary to check homomorphism.
		std::set<raw_term> edb(frozen_rr1.b[0].begin(), frozen_rr1.b[0].end());
		raw_prog nrp;
		nrp.r.push_back(rr2);
		
		// Run the queries and check for the frozen head. This process can
		// be optimized by inlining the frozen head of rule 1 into rule 2.
		std::set<raw_term> results;
		tables::run_prog(edb, nrp, d, opts, results);
		for(const raw_term &res : results) {
			if(res == frozen_rr1.h[0]) {
				// If the frozen head is found, then there is a homomorphism
				// between the two rules.
				return true;
			}
		}
		// If no frozen head found, then there is no homomorphism.
		return false;
	} else {
		return false;
	}
}

/* If rr1 and rr2 are both conjunctive bodies, check if there is a
 * homomorphism rr2 to rr1. By the homomorphism theorem, the existence
 * of a homomorphism implies that a valid substitution for rr1 can be
 * turned into a valid substitution for rr2. This function provides all
 * off them. */

bool driver::cbc(const raw_rule &rr1, raw_rule rr2,
		std::set<terms_hom> &homs) {
	// Get dictionary for generating fresh symbols
	dict_t &old_dict = tbl->get_dict();
	dict_t d;
	d.op = old_dict.op;
	d.cl = old_dict.cl;
	
	if(is_cq(rr1) && is_cq(rr2)) {
		// Freeze the variables and symbols of the rule we are checking the
		// containment of
		// Map from variables occuring in rr1 to frozen symbols
		std::map<elem, elem> freeze_map;
		raw_rule frozen_rr1 = freeze_rule(rr1, freeze_map, d);
		// Map from frozen symbols to variables occuring in rr1
		std::map<elem, elem> unfreeze_map;
		for(const auto &[k, v] : freeze_map) {
			unfreeze_map[v] = k;
		}
		
		// Build up the extensional database necessary to check homomorphism.
		std::set<raw_term> edb;
		// Map from term ids to terms in rr1
		std::map<elem, raw_term> term_map;
		int j = 0;
		// First put the frozen terms of rr1 into our containment program
		for(raw_term &rt : frozen_rr1.b[0]) {
			// Record the mapping from the term id to the raw_term it
			// represents
			elem term_id = elem::fresh_sym(d);
			term_map[term_id] = rr1.b[0][j++];
			// Mark our frozen term with an id so that we can trace the terms
			// involved in the homomorphism if it exists
			rt.e.insert(rt.e.begin() + 2, term_id);
			rt.calc_arity(nullptr);
			edb.insert(rt);
		}
		// Build up the query that proves the existence of a homomorphism
		// Make a new head for rr2 that exports all the variables used in
		// its body + ids of the frozen terms it binds to
		std::set<elem> rr2_body_vars_set;
		collect_vars(rr2.b[0].begin(), rr2.b[0].end(), rr2_body_vars_set);
		std::vector<elem> rr2_new_head = { elem::fresh_temp_sym(d), elem_openp };
		rr2_new_head.insert(rr2_new_head.end(), rr2_body_vars_set.begin(),
			rr2_body_vars_set.end());
		// Prepend term id variables to rr2's body terms and export the term
		// ids through the head
		for(raw_term &rt : rr2.b[0]) {
			// This variable will bind to the term id of a frozen body term
			// used in the homomorphism
			elem term_id = elem::fresh_var(d);
			rt.e.insert(rt.e.begin() + 2, term_id);
			rt.calc_arity(nullptr);
			rr2_new_head.push_back(term_id);
		}
		rr2_new_head.push_back(elem_closep);
		// Put body and head together and make containment program
		rr2.h[0] = raw_term(rr2_new_head);
		raw_prog nrp;
		nrp.r.push_back(rr2);
		
		// Run the queries and check for the frozen head. This process can
		// be optimized by inlining the frozen head of rule 1 into rule 2.
		std::set<raw_term> results;
		if(!tables::run_prog(edb, nrp, d, opts, results)) return false;
		for(const raw_term &res : results) {
			// If the result comes from the containment query (i.e. it is not
			// one of the frozen terms), then there is a homomorphism between
			// the bodies
			raw_term hd_src = rr2.h[0];
			if(res.e[0] == hd_src.e[0]) {
				var_subs var_map;
				std::set<raw_term> target_terms;
				// Now we want to express the homomorphism in terms of the
				// original (non-frozen) variables and terms of rr1.
				for(size_t i = 2; i < res.e.size() - 1; i++) {
					// If current variable is a body var
					if(rr2_body_vars_set.find(hd_src.e[i]) != rr2_body_vars_set.end()) {
						// Then trace the original var through the unfreeze map
						var_map[hd_src.e[i]] = at_default(unfreeze_map, res.e[i], res.e[i]);
					} else {
						// Otherwise trace the original term through the term map
						target_terms.insert(term_map[res.e[i]]);
					}
				}
				homs.insert(std::make_pair(target_terms, var_map));
			}
		}
		// If no results produced, then there is no homomorphism.
		return true;
	} else {
		return false;
	}
}

/* Given a homomorphism (i.e. a pair comprising variable substitutions
 * and terms surjected onto) and the rule that a homomorphism maps into,
 * determine which variables of the domain would be needed to express
 * constraints in the codomain. */
 
void driver::compute_required_vars(const raw_rule &rr,
		const terms_hom &hom, std::set<elem> &orig_vars) {
	auto &[rts, vs] = hom;
	// Get all the terms used by the given rule.
	std::set<raw_term> aggregate(rr.h.begin(), rr.h.end());
	aggregate.insert(rr.b[0].begin(), rr.b[0].end());
	// Make a vector containing all terms used by the given rule that are
	// not in homomorphism target.
	std::vector<raw_term> diff(aggregate.size());
	auto it = std::set_difference(aggregate.begin(), aggregate.end(),
		rts.begin(), rts.end(), diff.begin());
	diff.resize(it - diff.begin());
	// Get variables used outside homomorphism target
	std::set<elem> diff_vars;
	collect_vars(diff.begin(), diff.end(), diff_vars);
	// Get variables used inside homomorphism target
	std::set<elem> rts_vars;
	collect_vars(rts.begin(), rts.end(), rts_vars);
	// Compute the variables of the homomorphism target that we need to
	// retain control of
	std::vector<elem> nonfree_vars(diff_vars.size());
	auto jt = std::set_intersection(diff_vars.begin(), diff_vars.end(),
		rts_vars.begin(), rts_vars.end(), nonfree_vars.begin());
	nonfree_vars.resize(jt - nonfree_vars.begin());
	// Trace these variables of the homomorphism target to the
	// homomorphism source.
	for(auto &[var, covar] : vs) {
		if(std::find(nonfree_vars.begin(), nonfree_vars.end(), covar) !=
				nonfree_vars.end()) {
			orig_vars.insert(var);
		}
	}
}

/* Count the number of rules (including the given one) that derive facts
 * for the same relation that the given rule derives facts for. */

int_t driver::count_related_rules(const raw_rule &rr1, const raw_prog &rp) {
	int_t count = 0;
	for(const raw_rule &rr2 : rp.r) {
		if(rr1.h[0].e[0] == rr2.h[0].e[0] &&
				rr1.h[0].e.size() == rr2.h[0].e.size()) {
			count++;
		}
	}
	return count;
}

/* Takes two pure TML rules and returns true if the first is "smaller"
 * than the second. Smaller means less conjuncts in the body, and in the
 * case of a tie means less arguments in the head. */

bool rule_smaller(const raw_rule &rr2, const raw_rule &rr1) {
	if(rr1.b.size() == 1 && rr2.b.size() == 1) {
		if(rr1.b[0].size() == rr2.b[0].size()) {
			return rr1.h[0].e.size() > rr2.h[0].e.size();
		} else {
			return rr1.b[0].size() > rr2.b[0].size();
		}
	} else {
		return rr1.b.size() > rr2.b.size();
	}
}

/* Algorithm to factor the rules in a program using other rules.
 * Starting with the conjunctive rules with the biggest bodies, record
 * all the homomorphisms from this body into the bodies of other rules.
 * Afterwards, check if the head of this rule could be substituted
 * verbatim into the bodies of other rules, or whether a temporary
 * relation taking more arguments would be required. Afterwards,
 * replace the homomorphism targets with our chosen head. */

void driver::factor_rules(raw_prog &rp) {
	// Get dictionary for generating fresh symbols
	dict_t &d = tbl->get_dict();
	
	// Sort the rules so the biggest come first. Idea is that we want to
	// reduce total substitutions by doing the biggest factorizations
	// first. Also prioritizing rules with more arguments to reduce chance
	// that tmprel with more arguments is created.
	std::sort(rp.r.rbegin(), rp.r.rend(), rule_smaller);
	// The place where we temporarily store our temporary rules
	std::vector<raw_rule> pending_rules;
	// Go through the rules we want to try substituting into other
	for(raw_rule &rr2 : rp.r) {
		// Because we use a conjunctive homomorphism finding rule
		if(is_cq(rr2) && rr2.b[0].size() > 1) {
			// The variables of the current rule that we'd need to be able to
			// constrain/substitute into
			std::set<elem> needed_vars;
			std::set<std::tuple<raw_rule *, terms_hom>> agg;
			// Now let's look for rules that we can substitute the current
			// into
			for(raw_rule &rr1 : rp.r) {
				std::set<terms_hom> homs;
				// Find all the homomorphisms between outer and inner rule. This
				// way we can substitute the outer rule into the inner multiple
				// times.
				if(is_cq(rr1) && cbc(rr1, rr2, homs)) {
					for(const terms_hom &hom : homs) {
						auto &[target_terms, var_map] = hom;
						// Record only those homomorphisms where the target is at
						// least as big as the source for there is no point in
						// replacing a group of terms with a rule utilizing a bigger
						// group.
						if(target_terms.size() >= rr2.b[0].size()) {
							agg.insert(std::make_tuple(&rr1, hom));
							// If we were to substitute the target group of terms with
							// a single head, what arguments would we need to pass to
							// it?
							compute_required_vars(rr1, hom, needed_vars);
						}
					}
				}
			}
			
			// Now we need to figure out if we should create a temporary
			// relation containing body of current rule or whether we can just
			// use it directly. This depends on whether the head exports
			// enough variables.
			elem target_rel;
			std::vector<elem> target_args;
			std::set<elem> exported_vars;
			collect_vars(rr2.h[0], exported_vars);
			// Note whether we have created a temporary relation. Important
			// because we make the current rule depend on the temporary
			// relation in this case.
			bool tmp_rel =
				!((exported_vars == needed_vars && count_related_rules(rr2, rp) == 1) ||
					agg.size() == 1);
			
			if(tmp_rel) {
				// Variables are not exactly what is required. So make relation
				// exporting required variables and note argument order.
				target_rel = elem::fresh_temp_sym(d);
				target_args.assign(needed_vars.begin(), needed_vars.end());
				pending_rules.push_back(raw_rule(raw_term(target_rel, target_args), rr2.b[0]));
			} else {
				// The variables exported by current rule are exactly what is
				// needed by all homomorphisms from current body
				target_rel = rr2.h[0].e[0];
				for(size_t i = 2; i < rr2.h[0].e.size() - 1; i++) {
					target_args.push_back(rr2.h[0].e[i]);
				}
			}
			
			// Now we go through all the homomorphisms and try to apply
			// substitutions to their targets
			for(auto &[rr1, hom] : agg) {
				// If no temporary relation was created, then don't touch the
				// outer rule as its definition is irreducible.
				if(!tmp_rel && rr1 == &rr2) continue;
				auto &[rts, vs] = hom;
				std::set<raw_term> rr1_set(rr1->b[0].begin(), rr1->b[0].end());
				// If the target rule still includes the homomorphism target,
				// then ... . Note that this may not be the case as the targets
				// of several homomorphisms could overlap.
				if(std::includes(rr1_set.begin(), rr1_set.end(), rts.begin(),
						rts.end())) {
					// Remove the homomorphism target from the target rule
					auto it = std::set_difference(rr1_set.begin(), rr1_set.end(),
						rts.begin(), rts.end(), rr1->b[0].begin());
					rr1->b[0].resize(it - rr1->b[0].begin());
					// And place our chosen head with localized arguments.
					std::vector<elem> subbed_args;
					for(const elem &e : target_args) {
						// If the current parameter of the outer rule is a constant,
						// then just place it in our new term verbatim
						subbed_args.push_back(at_default(vs, e, e));
					}
					rr1->b[0].push_back(raw_term(target_rel, subbed_args));
				}
			}
		}
	}
	// Now add the pending rules. Done here to prevent movement of rules
	// during potential vector resizing.
	for(const raw_rule &rr : pending_rules) {
		rp.r.push_back(rr);
	}
}

/* Function to iterate through the partitions of the given set. Calls
 * the supplied function with a vector of sets representing each
 * partition. If the supplied function returns false, then the iteration
 * stops. */

template<typename T, typename F> bool partition_iter(std::set<T> &vars,
		std::vector<std::set<T>> &partitions, const F &f) {
	if(vars.empty()) {
		return f(partitions);
	} else {
		const T nvar = *vars.begin();
		vars.erase(nvar);
		for(size_t i = 0; i < partitions.size(); i++) {
			partitions[i].insert(nvar);
			if(!partition_iter(vars, partitions, f)) {
				return false;
			}
			partitions[i].erase(nvar);
		}
		std::set<T> npart = { nvar };
		partitions.push_back(npart);
		if(!partition_iter(vars, partitions, f)) {
			return false;
		}
		partitions.pop_back();
		vars.insert(nvar);
		return true;
	}
}

/* Function to iterate through the given set raised to the given
 * cartesian power. The supplied function is called with each tuple in
 * the product and if it returns false, the iteration stops. */

template<typename T, typename F>
		bool product_iter(const std::set<T> &vars, std::vector<T> &seq,
			size_t len, const F &f) {
	if(len == 0) {
		return f(seq);
	} else {
		for(const T &el : vars) {
			seq.push_back(el);
			if(!product_iter(vars, seq, len - 1, f)) {
				return false;
			}
			seq.pop_back();
		}
		return true;
	}
}

/* Function to iterate through the power set of the given set. The
 * supplied function is called with each element of the power set and
 * if it returns false, the iteration stops. */

template<typename T, typename F> bool power_iter(std::set<T> &elts,
		std::set<T> &subset, const F &f) {
	if(elts.size() == 0) {
		return f(subset);
	} else {
		const T nelt = *elts.begin();
		elts.erase(nelt);
		// Case where current element will not be in subset
		if(!power_iter(elts, subset, f)) {
			return false;
		}
		if(subset.insert(nelt).second) {
			// Case where current element will be in subset
			if(!power_iter(elts, subset, f)) {
				return false;
			}
			subset.erase(nelt);
		}
		elts.insert(nelt);
		return true;
	}
}

/* Collect the variables used in the given terms and return. */

void driver::collect_vars(const raw_term &rt, std::set<elem> &vars) {
	for(const elem &e : rt.e) {
		if(e.type == elem::VAR) {
			vars.insert(e);
		}
	}
}

/* Collect the variables used in the given terms and return. */

template <class InputIterator>
		void driver::collect_vars(InputIterator first, InputIterator last,
			std::set<elem> &vars) {
	for(; first != last; first++) {
		collect_vars(*first, vars);
	}
}

/* Collect the variables used in the head and the positive terms of the
 * given rule and return. */

void driver::collect_positive_vars(const raw_rule &rr,
		std::set<elem> &vars) {
	collect_vars(rr.h[0], vars);
	for(const raw_term &tm : rr.b[0]) {
		if(!tm.neg) {
			collect_vars(tm, vars);
		}
	}
}

/* If rr1 and rr2 are both conjunctive queries with negation, check that
 * rr1 is contained by rr2. Do this using the Levy-Sagiv test. */

bool driver::cqnc(const raw_rule &rr1, const raw_rule &rr2) {
	// The CQNC test is very heavy, so try to use the lighter CQC test if
	// possible.
	if(is_cq(rr1) && is_cq(rr2)) return cqc(rr1, rr2);
	// Check that rules have correct format
	if(!(is_cqn(rr1) && is_cqn(rr2) &&
		get_relation_info(rr1.h[0]) == get_relation_info(rr2.h[0]))) return false;
	
	// Get dictionary for generating fresh symbols
	dict_t &old_dict = tbl->get_dict();
	
	std::set<elem> vars;
	collect_positive_vars(rr1, vars);
	std::vector<std::set<elem>> partitions;
	// Do the Levy-Sagiv test
	return partition_iter(vars, partitions,
		[&](const std::vector<std::set<elem>> &partitions) -> bool {
			dict_t d;
			d.op = old_dict.op;
			d.cl = old_dict.cl;
			// Map each variable to a fresh symbol according to the partitions
			std::map<elem, elem> subs;
			for(const std::set<elem> &part : partitions) {
				elem pvar = elem::fresh_sym(d);
				for(const elem &e : part) {
					subs[e] = pvar;
				}
			}
			raw_rule subbed = freeze_rule(rr1, subs, d);
			std::set<elem> symbol_set;
			std::set<raw_term> canonical, canonical_negative;
			// Separate the positive and negative subgoals. Note the symbols
			// supplied to the subgoals.
			for(raw_term &rt : subbed.b[0]) {
				if(rt.neg) {
					rt.neg = false;
					canonical_negative.insert(rt);
					rt.neg = true;
				} else {
					canonical.insert(rt);
				}
				for(size_t i = 2; i < rt.e.size() - 1; i++) {
					symbol_set.insert(rt.e[i]);
				}
			}
			// Note the symbols supplied to the head.
			for(raw_term &rt : subbed.h) {
				for(size_t i = 2; i < rt.e.size() - 1; i++) {
					symbol_set.insert(rt.e[i]);
				}
			}
			// Does canonical make all the subgoals of subbed true?
			for(raw_term &rt : subbed.b[0]) {
				if(rt.neg) {
					// If the term in the rule is negated, we need to make sure
					// that it is not in the canonical database.
					rt.neg = false;
					if(canonical.find(rt) != canonical.end()) {
						return true;
					}
					rt.neg = true;
				}
			}
			// Now we need to get the largest superset of our canonical
			// database
			std::set<raw_term> superset;
			for(const raw_term &rt : rr2.b[0]) {
				std::vector<elem> tuple;
				product_iter(symbol_set, tuple, rt.e.size() - 3,
					[&](const std::vector<elem> tuple) -> bool {
						std::vector<elem> nterm_e = { rt.e[0], rt.e[1] };
						for(const elem &e : tuple) {
							nterm_e.push_back(e);
						}
						nterm_e.push_back(rt.e[rt.e.size() - 1]);
						raw_term nterm(nterm_e);
						superset.insert(nterm);
						return true;
					});
			}
			// Remove the frozen negative subgoals
			for(const raw_term &rt : canonical_negative) {
				superset.erase(rt);
			}
			// Now need to through all the supersets of our canonical database
			// and check that they yield the frozen head.
			return power_iter(superset, canonical,
				[&](const std::set<raw_term> ext) -> bool {
					raw_prog test_prog;
					test_prog.r.push_back(rr2);
					std::set<raw_term> res;
					tables::run_prog(ext, test_prog, d, opts, res);
					return res.find(subbed.h[0]) != res.end();
				});
		});
}

/* If the given query is conjunctive, go through its terms and see if
 * removing one of them can produce an equivalent query. If this is
 * the case, modify the input query and indicate that this has happened
 * through the return flag. */

bool driver::try_minimize(raw_rule &rr) {
	if(is_cqn(rr)) {
		std::vector<raw_term> heads1 = rr.h, bodie1 = rr.b[0],
			heads2 = rr.h, bodie2 = rr.b[0];
		// Let's see if we can remove a body term from the rule without
		// affecting its behavior
		for(size_t i = 0; i < bodie1.size(); i++) {
			// bodie2 is currently equal to bodie1
			bodie2.erase(bodie2.begin() + i);
			// bodie2 missing element i, meaning that rule 2 contains rule 1
			// Construct our candidate replacement rule
			raw_rule rr2(heads2, bodie2);
			if(cqnc(rr2, rr)) {
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

/* Go through the program and removed those queries that are subsumed by
 * others. While we're at it, minimize (i.e. subsume a query with its
 * part) the shortlisted queries to reduce time cost of future
 * subsumptions. This function does not respect order, so it should only
 * be used on an unordered stratum. */

void driver::subsume_queries(raw_prog &rp) {
	std::vector<raw_rule> reduced_rules;
	for(raw_rule &rr : rp.r) {
		bool subsumed = false;
		
		for(std::vector<raw_rule>::iterator nrr = reduced_rules.begin();
				nrr != reduced_rules.end();) {
			if(cqnc(rr, *nrr)) {
				// If the current rule is contained by a rule in reduced rules,
				// then move onto the next rule in the outer loop
				subsumed = true;
				break;
			} else if(cqnc(*nrr, rr)) {
				// If current rule contains that in reduced rules, then remove
				// the subsumed rule from reduced rules
				nrr = reduced_rules.erase(nrr);
			} else {
				// Neither rule contains the other. Move on.
				nrr++;
			}
		}
		if(!subsumed) {
			// Do the maximal amount of query minimization on the query we are
			// about to admit. This should reduce the time cost of future
			// subsumptions.
			while(try_minimize(rr));
			// If the current rule has not been subsumed, then it needs to be
			// represented in the reduced rules.
			reduced_rules.push_back(rr);
		}
	}
	rp.r = reduced_rules;
}

void driver::simplify_formulas(raw_prog &rp) {
	for(raw_rule &rr : rp.r) {
		if(!rr.is_b()) {
			sprawformtree prft = rr.get_prft();
			rr.set_prft(raw_form_tree::simplify(prft));
		}
	}
}

/* In the case that the argument is a variable, get the symbol
 * associated with it and return that. If there is no such association,
 * make one. */

elem driver::quote_elem(const elem &e, std::map<elem, elem> &variables,
		dict_t &d) {
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

raw_rule driver::freeze_rule(raw_rule rr,
		std::map<elem, elem> &freeze_map, dict_t &d) {
	for(raw_term &tm : rr.h) {
		for(elem &el : tm.e) {
			el = quote_elem(el, freeze_map, d);
		}
	}
	for(std::vector<raw_term> &bodie : rr.b) {
		for(raw_term &tm : bodie) {
			for(elem &el : tm.e) {
				el = quote_elem(el, freeze_map, d);
			}
		}
	}
	return rr;
}

/* Takes a raw term and returns its quotation within a relation of the
 * given name. The names of variable elements within the raw term are
 * added to the variables map. */

elem driver::quote_term(const raw_term &head, const elem &rel_name,
		const elem &domain_name, raw_prog &rp, std::map<elem, elem> &variables) {
	// Get dictionary for generating fresh symbols
	dict_t &d = tbl->get_dict();
	elem term_id = elem::fresh_sym(d);
	if(head.extype == raw_term::REL) {
		// Add metadata to quoted term: term signature, term id, term name
		std::vector<elem> quoted_term_e = {rel_name, elem_openp, elem(QTERM),
			term_id, head.e[0] };
		
		for(int_t param_idx = 2; param_idx < ssize(head.e) - 1; param_idx ++) {
			quoted_term_e.push_back(quote_elem(head.e[param_idx], variables, d));
		}
		// Terminate term elements and make raw_term object
		quoted_term_e.push_back(elem_closep);
		rp.r.push_back(raw_rule(raw_term(quoted_term_e)));
	} else if(head.extype == raw_term::EQ) {
		// Add metadata to quoted term: term signature, term id, term name
		std::vector<elem> quoted_term_e = {rel_name, elem_openp, elem(QEQUALS),
			term_id, quote_elem(head.e[0], variables, d),
			quote_elem(head.e[2], variables, d), elem_closep };
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

/* Recursively quotes the given formula. Say that the output relation
 * name is q, quote_formula will populate it according to the following
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

elem driver::quote_formula(const sprawformtree &t, const elem &rel_name,
		const elem &domain_name, raw_prog &rp, std::map<elem, elem> &variables) {
	// Get dictionary for generating fresh symbols
	dict_t &d = tbl->get_dict();
	const elem part_id = elem::fresh_sym(d);
	switch(t->type) {
		case elem::IMPLIES:
			rp.r.push_back(raw_rule(raw_term({rel_name, elem_openp, elem(QIMPLIES),
				part_id, quote_formula(t->l, rel_name, domain_name, rp, variables),
				quote_formula(t->r, rel_name, domain_name, rp, variables), elem_closep })));
			break;
		case elem::COIMPLIES:
			rp.r.push_back(raw_rule(raw_term({rel_name, elem_openp, elem(QCOIMPLIES),
				part_id, quote_formula(t->l, rel_name, domain_name, rp, variables),
				quote_formula(t->r, rel_name, domain_name, rp, variables), elem_closep })));
			break;
		case elem::AND:
			rp.r.push_back(raw_rule(raw_term({rel_name, elem_openp, elem(QAND),
				part_id, quote_formula(t->l, rel_name, domain_name, rp, variables),
				quote_formula(t->r, rel_name, domain_name, rp, variables), elem_closep })));
			break;
		case elem::ALT:
			rp.r.push_back(raw_rule(raw_term({rel_name, elem_openp, elem(QALT),
				part_id, quote_formula(t->l, rel_name, domain_name, rp, variables),
				quote_formula(t->r, rel_name, domain_name, rp, variables), elem_closep })));
			break;
		case elem::NOT:
			rp.r.push_back(raw_rule(raw_term({rel_name, elem_openp, elem(QNOT),
				part_id, quote_formula(t->l, rel_name, domain_name, rp, variables),
				elem_closep })));
			break;
		case elem::EXISTS: {
			elem qvar = quote_elem(*(t->l->el), variables, d);
			rp.r.push_back(raw_rule(raw_term({rel_name, elem_openp,
				elem(QEXISTS), part_id, qvar,
				quote_formula(t->r, rel_name, domain_name, rp, variables), elem_closep })));
			break;
		} case elem::UNIQUE: {
			elem qvar = quote_elem(*(t->l->el), variables, d);
			rp.r.push_back(raw_rule(raw_term({rel_name, elem_openp,
				elem(QUNIQUE), part_id, qvar,
				quote_formula(t->r, rel_name, domain_name, rp, variables), elem_closep })));
			break;
		} case elem::NONE: {
			return quote_term(*t->rt, rel_name, domain_name, rp, variables);
			break;
		} case elem::FORALL: {
			elem qvar = quote_elem(*(t->l->el), variables, d);
			rp.r.push_back(raw_rule(raw_term({rel_name, elem_openp,
				elem(QFORALL), part_id, qvar,
				quote_formula(t->r, rel_name, domain_name, rp, variables), elem_closep })));
			break;
		} default:
			assert(false); //should never reach here
	}
	return part_id;
}

/* Quote the given rule and put its quotation into the given raw_prog
 * under a relation given by rel_name. */

std::vector<elem> driver::quote_rule(const raw_rule &rr,
		const elem &rel_name, const elem &domain_name, raw_prog &rp,
		std::map<elem, elem> &variables) {
	// Get dictionary for generating fresh symbols
	dict_t &d = tbl->get_dict();
	std::vector<elem> rule_ids;
	const elem body_id = quote_formula(rr.get_prft(), rel_name, domain_name, rp, variables);
	for(int_t gidx = 0; gidx < ssize(rr.h); gidx++) {
		const elem head_id = quote_term(rr.h[gidx], rel_name, domain_name, rp, variables);
		const elem rule_id = elem::fresh_sym(d);
		rp.r.push_back(raw_rule(raw_term({rel_name, elem_openp, elem(QRULE),
			rule_id, head_id, body_id, elem_closep })));
		rule_ids.push_back(rule_id);
	}
	return rule_ids;
}

/* Put the quotation of the given program into a relation of the given
 * name in the given program. */

void driver::quote_prog(const raw_prog nrp, const elem &rel_name,
		const elem &domain_name, raw_prog &rp) {
	// Maintain a list of the variable substitutions:
	std::map<elem, elem> variables;
	for(int_t ridx = 0; ridx < ssize(nrp.r); ridx++) {
		quote_rule(nrp.r[ridx], rel_name, domain_name, rp, variables);
	}
	// Now create sub-relation to store the names of the variable
	// substitutes in the quoted relation
	for(auto const& [_, var_sym] : variables) {
		rp.r.push_back(raw_rule(raw_term({ rel_name, elem_openp,
			elem(QVARS), var_sym, elem_closep })));
	}
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
 * it's second argument is the program to quote. */

void driver::transform_quotes(raw_prog &rp) {
	for(size_t oridx = 0; oridx < rp.r.size(); oridx++) {
		// Iterate through the bodies of the current rule looking for uses
		// of the "eval" relation.
		for(const raw_term &curr_term : rp.r[oridx].h) {
			if(!(!curr_term.e.empty() && curr_term.e[0].type == elem::SYM &&
				to_string_t("quote") == lexeme2str(curr_term.e[0].e))) continue;
			// The first parenthesis marks the beginning of eval's three arguments.
			if(!(ssize(curr_term.e) == 6 && curr_term.e[1].type == elem::OPENP &&
				curr_term.e[5].type == elem::CLOSEP)) continue;
			// The relation to contain the evaled relation is the first symbol
			// between the parentheses
			elem out_rel = curr_term.e[2];
			// The relation containing the quotation arity is the second symbol
			// between the parentheses
			elem domain_sym = curr_term.e[3];
			// The formal symbol representing the quotation relation is the
			// third symbol between the parentheses
			elem quote_str = curr_term.e[4];
			
			if(quote_str.type == elem::STR && quote_str.e[1] > quote_str.e[0] &&
					*quote_str.e[0] == '`') {
				raw_prog nrp = read_prog(quote_str, rp);
				// Create the quotation relation
				quote_prog(nrp, out_rel, domain_sym, rp);
			}
		}
	}
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
			elem domain_sym = curr_term.e[3];
			// The formal symbol representing the quotation relation is the
			// third symbol between the parentheses
			elem quote_sym = curr_term.e[4];
			// Get dictionary for generating fresh variables
			dict_t &d = tbl->get_dict();
			// This symbol is used when the variable allocation is finished
			elem und_sym = elem::fresh_sym(d);
			// This relation will house most of the interpreter
			elem aux_rel = elem::fresh_temp_sym(d);
			// This relation will be used to fix interpretations to literals
			elem fs_rel = elem::fresh_temp_sym(d);
			// This relation will be used to fix interpretations to each other
			elem fv_rel = elem::fresh_temp_sym(d);
			
			{
				elem e0;
				e0.type = elem::SYM;
				e0.e = d.get_lexeme("FORMULA_NODE");
				elem e1;
				e1.type = elem::OPENP;
				e1.e = d.get_lexeme("(");
				elem e2;
				e2.type = elem::VAR;
				e2.e = d.get_lexeme("?id");
				elem e3;
				e3.type = elem::CLOSEP;
				e3.e = d.get_lexeme(")");
				raw_term rt4;
				rt4.neg = false;
				rt4.extype = raw_term::REL;
				rt4.e.push_back(e0);
				rt4.e.push_back(e1);
				rt4.e.push_back(e2);
				rt4.e.push_back(e3);
				rt4.calc_arity(nullptr);
				elem &e6 = quote_sym;
				elem e7;
				e7.type = elem::SYM;
				e7.e = d.get_lexeme("TERM");
				raw_term rt8;
				rt8.neg = false;
				rt8.extype = raw_term::REL;
				rt8.e.push_back(e6);
				rt8.e.push_back(e1);
				rt8.e.push_back(e7);
				rt8.e.push_back(e2);
				rt8.e.push_back(e3);
				rt8.calc_arity(nullptr);
				sprawformtree ft5 = std::make_shared<raw_form_tree>(elem::NONE, rt8);
				raw_rule rr9;
				rr9.h.push_back(rt4);
				rr9.set_prft(ft5);
				raw_term rt10;
				rt10.neg = false;
				rt10.extype = raw_term::REL;
				rt10.e.push_back(e0);
				rt10.e.push_back(e1);
				rt10.e.push_back(e2);
				rt10.e.push_back(e3);
				rt10.calc_arity(nullptr);
				elem e12;
				e12.type = elem::SYM;
				e12.e = d.get_lexeme("EQUALS");
				elem e13;
				e13.type = elem::VAR;
				e13.e = d.get_lexeme("?p1");
				elem e14;
				e14.type = elem::VAR;
				e14.e = d.get_lexeme("?p2");
				raw_term rt15;
				rt15.neg = false;
				rt15.extype = raw_term::REL;
				rt15.e.push_back(e6);
				rt15.e.push_back(e1);
				rt15.e.push_back(e12);
				rt15.e.push_back(e2);
				rt15.e.push_back(e13);
				rt15.e.push_back(e14);
				rt15.e.push_back(e3);
				rt15.calc_arity(nullptr);
				sprawformtree ft11 = std::make_shared<raw_form_tree>(elem::NONE, rt15);
				raw_rule rr16;
				rr16.h.push_back(rt10);
				rr16.set_prft(ft11);
				raw_term rt17;
				rt17.neg = false;
				rt17.extype = raw_term::REL;
				rt17.e.push_back(e0);
				rt17.e.push_back(e1);
				rt17.e.push_back(e2);
				rt17.e.push_back(e3);
				rt17.calc_arity(nullptr);
				elem e19;
				e19.type = elem::SYM;
				e19.e = d.get_lexeme("AND");
				elem e20;
				e20.type = elem::VAR;
				e20.e = d.get_lexeme("?b1");
				elem e21;
				e21.type = elem::VAR;
				e21.e = d.get_lexeme("?b2");
				raw_term rt22;
				rt22.neg = false;
				rt22.extype = raw_term::REL;
				rt22.e.push_back(e6);
				rt22.e.push_back(e1);
				rt22.e.push_back(e19);
				rt22.e.push_back(e2);
				rt22.e.push_back(e20);
				rt22.e.push_back(e21);
				rt22.e.push_back(e3);
				rt22.calc_arity(nullptr);
				sprawformtree ft18 = std::make_shared<raw_form_tree>(elem::NONE, rt22);
				raw_rule rr23;
				rr23.h.push_back(rt17);
				rr23.set_prft(ft18);
				raw_term rt24;
				rt24.neg = false;
				rt24.extype = raw_term::REL;
				rt24.e.push_back(e0);
				rt24.e.push_back(e1);
				rt24.e.push_back(e2);
				rt24.e.push_back(e3);
				rt24.calc_arity(nullptr);
				elem e26;
				e26.type = elem::SYM;
				e26.e = d.get_lexeme("OR");
				raw_term rt27;
				rt27.neg = false;
				rt27.extype = raw_term::REL;
				rt27.e.push_back(e6);
				rt27.e.push_back(e1);
				rt27.e.push_back(e26);
				rt27.e.push_back(e2);
				rt27.e.push_back(e20);
				rt27.e.push_back(e21);
				rt27.e.push_back(e3);
				rt27.calc_arity(nullptr);
				sprawformtree ft25 = std::make_shared<raw_form_tree>(elem::NONE, rt27);
				raw_rule rr28;
				rr28.h.push_back(rt24);
				rr28.set_prft(ft25);
				raw_term rt29;
				rt29.neg = false;
				rt29.extype = raw_term::REL;
				rt29.e.push_back(e0);
				rt29.e.push_back(e1);
				rt29.e.push_back(e2);
				rt29.e.push_back(e3);
				rt29.calc_arity(nullptr);
				elem e31;
				e31.type = elem::SYM;
				e31.e = d.get_lexeme("TRUE");
				raw_term rt32;
				rt32.neg = false;
				rt32.extype = raw_term::REL;
				rt32.e.push_back(e6);
				rt32.e.push_back(e1);
				rt32.e.push_back(e31);
				rt32.e.push_back(e2);
				rt32.e.push_back(e3);
				rt32.calc_arity(nullptr);
				sprawformtree ft30 = std::make_shared<raw_form_tree>(elem::NONE, rt32);
				raw_rule rr33;
				rr33.h.push_back(rt29);
				rr33.set_prft(ft30);
				elem e34;
				e34.type = elem::SYM;
				e34.e = d.get_lexeme("RULE_NODE");
				raw_term rt35;
				rt35.neg = false;
				rt35.extype = raw_term::REL;
				rt35.e.push_back(e34);
				rt35.e.push_back(e1);
				rt35.e.push_back(e2);
				rt35.e.push_back(e3);
				rt35.calc_arity(nullptr);
				elem e37;
				e37.type = elem::SYM;
				e37.e = d.get_lexeme("RULE");
				elem e38;
				e38.type = elem::VAR;
				e38.e = d.get_lexeme("?h");
				elem e39;
				e39.type = elem::VAR;
				e39.e = d.get_lexeme("?b");
				raw_term rt40;
				rt40.neg = false;
				rt40.extype = raw_term::REL;
				rt40.e.push_back(e6);
				rt40.e.push_back(e1);
				rt40.e.push_back(e37);
				rt40.e.push_back(e2);
				rt40.e.push_back(e38);
				rt40.e.push_back(e39);
				rt40.e.push_back(e3);
				rt40.calc_arity(nullptr);
				sprawformtree ft36 = std::make_shared<raw_form_tree>(elem::NONE, rt40);
				raw_rule rr41;
				rr41.h.push_back(rt35);
				rr41.set_prft(ft36);
				elem e42;
				e42.type = elem::SYM;
				e42.e = d.get_lexeme("COMMIT");
				raw_term rt43;
				rt43.neg = false;
				rt43.extype = raw_term::REL;
				rt43.e.push_back(e42);
				rt43.e.push_back(e1);
				rt43.e.push_back(e3);
				rt43.calc_arity(nullptr);
				elem e44;
				e44.type = elem::SYM;
				e44.e = d.get_lexeme("EXECUTE");
				raw_term rt45;
				rt45.neg = true;
				rt45.extype = raw_term::REL;
				rt45.e.push_back(e44);
				rt45.e.push_back(e1);
				rt45.e.push_back(e3);
				rt45.calc_arity(nullptr);
				elem e46;
				e46.type = elem::SYM;
				e46.e = d.get_lexeme("RULE_DONE");
				elem e47;
				e47.type = elem::VAR;
				e47.e = d.get_lexeme("?y");
				raw_term rt48;
				rt48.neg = true;
				rt48.extype = raw_term::REL;
				rt48.e.push_back(e46);
				rt48.e.push_back(e1);
				rt48.e.push_back(e47);
				rt48.e.push_back(e3);
				rt48.calc_arity(nullptr);
				elem e52;
				e52.type = elem::SYM;
				e52.e = d.get_lexeme("EXECUTE2");
				raw_term rt53;
				rt53.neg = false;
				rt53.extype = raw_term::REL;
				rt53.e.push_back(e52);
				rt53.e.push_back(e1);
				rt53.e.push_back(e3);
				rt53.calc_arity(nullptr);
				sprawformtree ft51 = std::make_shared<raw_form_tree>(elem::NONE, rt53);
				raw_term rt56;
				rt56.neg = false;
				rt56.extype = raw_term::REL;
				rt56.e.push_back(e42);
				rt56.e.push_back(e1);
				rt56.e.push_back(e3);
				rt56.calc_arity(nullptr);
				sprawformtree ft55 = std::make_shared<raw_form_tree>(elem::NONE, rt56);
				sprawformtree ft54 = std::make_shared<raw_form_tree>(elem::NOT, ft55);
				sprawformtree ft50 = std::make_shared<raw_form_tree>(elem::AND, ft51, ft54);
				elem e59;
				e59.type = elem::VAR;
				e59.e = d.get_lexeme("?x");
				sprawformtree ft58 = std::make_shared<raw_form_tree>(elem::VAR, e59);
				elem e62;
				e62.type = elem::VAR;
				e62.e = d.get_lexeme("?z");
				sprawformtree ft61 = std::make_shared<raw_form_tree>(elem::VAR, e62);
				raw_term rt65;
				rt65.neg = false;
				rt65.extype = raw_term::REL;
				rt65.e.push_back(e0);
				rt65.e.push_back(e1);
				rt65.e.push_back(e59);
				rt65.e.push_back(e3);
				rt65.calc_arity(nullptr);
				sprawformtree ft64 = std::make_shared<raw_form_tree>(elem::NONE, rt65);
				elem e67;
				e67.type = elem::SYM;
				e67.e = d.get_lexeme("FORMULA_DONE");
				raw_term rt68;
				rt68.neg = false;
				rt68.extype = raw_term::REL;
				rt68.e.push_back(e67);
				rt68.e.push_back(e1);
				rt68.e.push_back(e59);
				rt68.e.push_back(e62);
				rt68.e.push_back(e3);
				rt68.calc_arity(nullptr);
				sprawformtree ft66 = std::make_shared<raw_form_tree>(elem::NONE, rt68);
				sprawformtree ft63 = std::make_shared<raw_form_tree>(elem::IMPLIES, ft64, ft66);
				sprawformtree ft60 = std::make_shared<raw_form_tree>(elem::EXISTS, ft61, ft63);
				sprawformtree ft57 = std::make_shared<raw_form_tree>(elem::FORALL, ft58, ft60);
				sprawformtree ft49 = std::make_shared<raw_form_tree>(elem::AND, ft50, ft57);
				raw_rule rr69;
				rr69.h.push_back(rt43);
				rr69.h.push_back(rt45);
				rr69.h.push_back(rt48);
				rr69.set_prft(ft49);
				elem e70;
				e70.type = elem::SYM;
				e70.e = d.get_lexeme("COMMIT2");
				raw_term rt71;
				rt71.neg = false;
				rt71.extype = raw_term::REL;
				rt71.e.push_back(e70);
				rt71.e.push_back(e1);
				rt71.e.push_back(e3);
				rt71.calc_arity(nullptr);
				raw_term rt73;
				rt73.neg = false;
				rt73.extype = raw_term::REL;
				rt73.e.push_back(e42);
				rt73.e.push_back(e1);
				rt73.e.push_back(e3);
				rt73.calc_arity(nullptr);
				sprawformtree ft72 = std::make_shared<raw_form_tree>(elem::NONE, rt73);
				raw_rule rr74;
				rr74.h.push_back(rt71);
				rr74.set_prft(ft72);
				raw_term rt75;
				rt75.neg = true;
				rt75.extype = raw_term::REL;
				rt75.e.push_back(e52);
				rt75.e.push_back(e1);
				rt75.e.push_back(e3);
				rt75.calc_arity(nullptr);
				raw_term rt77;
				rt77.neg = false;
				rt77.extype = raw_term::REL;
				rt77.e.push_back(e42);
				rt77.e.push_back(e1);
				rt77.e.push_back(e3);
				rt77.calc_arity(nullptr);
				sprawformtree ft76 = std::make_shared<raw_form_tree>(elem::NONE, rt77);
				raw_rule rr78;
				rr78.h.push_back(rt75);
				rr78.set_prft(ft76);
				raw_term rt79;
				rt79.neg = false;
				rt79.extype = raw_term::REL;
				rt79.e.push_back(e44);
				rt79.e.push_back(e1);
				rt79.e.push_back(e3);
				rt79.calc_arity(nullptr);
				raw_term rt80;
				rt80.neg = true;
				rt80.extype = raw_term::REL;
				rt80.e.push_back(e42);
				rt80.e.push_back(e1);
				rt80.e.push_back(e3);
				rt80.calc_arity(nullptr);
				raw_term rt81;
				rt81.neg = true;
				rt81.extype = raw_term::REL;
				rt81.e.push_back(e67);
				rt81.e.push_back(e1);
				rt81.e.push_back(e47);
				rt81.e.push_back(e3);
				rt81.calc_arity(nullptr);
				raw_term rt85;
				rt85.neg = false;
				rt85.extype = raw_term::REL;
				rt85.e.push_back(e70);
				rt85.e.push_back(e1);
				rt85.e.push_back(e3);
				rt85.calc_arity(nullptr);
				sprawformtree ft84 = std::make_shared<raw_form_tree>(elem::NONE, rt85);
				raw_term rt88;
				rt88.neg = false;
				rt88.extype = raw_term::REL;
				rt88.e.push_back(e44);
				rt88.e.push_back(e1);
				rt88.e.push_back(e3);
				rt88.calc_arity(nullptr);
				sprawformtree ft87 = std::make_shared<raw_form_tree>(elem::NONE, rt88);
				sprawformtree ft86 = std::make_shared<raw_form_tree>(elem::NOT, ft87);
				sprawformtree ft83 = std::make_shared<raw_form_tree>(elem::AND, ft84, ft86);
				sprawformtree ft90 = std::make_shared<raw_form_tree>(elem::VAR, e59);
				raw_term rt93;
				rt93.neg = false;
				rt93.extype = raw_term::REL;
				rt93.e.push_back(e34);
				rt93.e.push_back(e1);
				rt93.e.push_back(e59);
				rt93.e.push_back(e3);
				rt93.calc_arity(nullptr);
				sprawformtree ft92 = std::make_shared<raw_form_tree>(elem::NONE, rt93);
				raw_term rt95;
				rt95.neg = false;
				rt95.extype = raw_term::REL;
				rt95.e.push_back(e46);
				rt95.e.push_back(e1);
				rt95.e.push_back(e59);
				rt95.e.push_back(e3);
				rt95.calc_arity(nullptr);
				sprawformtree ft94 = std::make_shared<raw_form_tree>(elem::NONE, rt95);
				sprawformtree ft91 = std::make_shared<raw_form_tree>(elem::IMPLIES, ft92, ft94);
				sprawformtree ft89 = std::make_shared<raw_form_tree>(elem::FORALL, ft90, ft91);
				sprawformtree ft82 = std::make_shared<raw_form_tree>(elem::AND, ft83, ft89);
				raw_rule rr96;
				rr96.h.push_back(rt79);
				rr96.h.push_back(rt80);
				rr96.h.push_back(rt81);
				rr96.set_prft(ft82);
				raw_term rt97;
				rt97.neg = false;
				rt97.extype = raw_term::REL;
				rt97.e.push_back(e52);
				rt97.e.push_back(e1);
				rt97.e.push_back(e3);
				rt97.calc_arity(nullptr);
				raw_term rt99;
				rt99.neg = false;
				rt99.extype = raw_term::REL;
				rt99.e.push_back(e44);
				rt99.e.push_back(e1);
				rt99.e.push_back(e3);
				rt99.calc_arity(nullptr);
				sprawformtree ft98 = std::make_shared<raw_form_tree>(elem::NONE, rt99);
				raw_rule rr100;
				rr100.h.push_back(rt97);
				rr100.set_prft(ft98);
				raw_term rt101;
				rt101.neg = true;
				rt101.extype = raw_term::REL;
				rt101.e.push_back(e70);
				rt101.e.push_back(e1);
				rt101.e.push_back(e3);
				rt101.calc_arity(nullptr);
				raw_term rt103;
				rt103.neg = false;
				rt103.extype = raw_term::REL;
				rt103.e.push_back(e44);
				rt103.e.push_back(e1);
				rt103.e.push_back(e3);
				rt103.calc_arity(nullptr);
				sprawformtree ft102 = std::make_shared<raw_form_tree>(elem::NONE, rt103);
				raw_rule rr104;
				rr104.h.push_back(rt101);
				rr104.set_prft(ft102);
				elem e105;
				e105.type = elem::SYM;
				e105.e = d.get_lexeme("COUNTDOWN0");
				raw_term rt106;
				rt106.neg = false;
				rt106.extype = raw_term::REL;
				rt106.e.push_back(e105);
				rt106.e.push_back(e1);
				rt106.e.push_back(e3);
				rt106.calc_arity(nullptr);
				elem e108;
				e108.type = elem::NUM;
				e108.num = 0;
				elem e109;
				e109.type = elem::EQ;
				e109.e = d.get_lexeme("=");
				raw_term rt110;
				rt110.neg = false;
				rt110.extype = raw_term::EQ;
				rt110.e.push_back(e108);
				rt110.e.push_back(e109);
				rt110.e.push_back(e108);
				rt110.calc_arity(nullptr);
				sprawformtree ft107 = std::make_shared<raw_form_tree>(elem::NONE, rt110);
				raw_rule rr111;
				rr111.h.push_back(rt106);
				elem e112;
				e112.type = elem::SYM;
				e112.e = d.get_lexeme("COUNTDOWN1");
				raw_term rt113;
				rt113.neg = false;
				rt113.extype = raw_term::REL;
				rt113.e.push_back(e112);
				rt113.e.push_back(e1);
				rt113.e.push_back(e3);
				rt113.calc_arity(nullptr);
				raw_term rt115;
				rt115.neg = false;
				rt115.extype = raw_term::REL;
				rt115.e.push_back(e105);
				rt115.e.push_back(e1);
				rt115.e.push_back(e3);
				rt115.calc_arity(nullptr);
				sprawformtree ft114 = std::make_shared<raw_form_tree>(elem::NONE, rt115);
				raw_rule rr116;
				rr116.h.push_back(rt113);
				rr116.set_prft(ft114);
				elem e117;
				e117.type = elem::SYM;
				e117.e = d.get_lexeme("COUNTDOWN2");
				raw_term rt118;
				rt118.neg = false;
				rt118.extype = raw_term::REL;
				rt118.e.push_back(e117);
				rt118.e.push_back(e1);
				rt118.e.push_back(e3);
				rt118.calc_arity(nullptr);
				raw_term rt120;
				rt120.neg = false;
				rt120.extype = raw_term::REL;
				rt120.e.push_back(e112);
				rt120.e.push_back(e1);
				rt120.e.push_back(e3);
				rt120.calc_arity(nullptr);
				sprawformtree ft119 = std::make_shared<raw_form_tree>(elem::NONE, rt120);
				raw_rule rr121;
				rr121.h.push_back(rt118);
				rr121.set_prft(ft119);
				elem e122;
				e122.type = elem::SYM;
				e122.e = d.get_lexeme("COUNTDOWN3");
				raw_term rt123;
				rt123.neg = false;
				rt123.extype = raw_term::REL;
				rt123.e.push_back(e122);
				rt123.e.push_back(e1);
				rt123.e.push_back(e3);
				rt123.calc_arity(nullptr);
				raw_term rt125;
				rt125.neg = false;
				rt125.extype = raw_term::REL;
				rt125.e.push_back(e117);
				rt125.e.push_back(e1);
				rt125.e.push_back(e3);
				rt125.calc_arity(nullptr);
				sprawformtree ft124 = std::make_shared<raw_form_tree>(elem::NONE, rt125);
				raw_rule rr126;
				rr126.h.push_back(rt123);
				rr126.set_prft(ft124);
				elem e127;
				e127.type = elem::SYM;
				e127.e = d.get_lexeme("COUNTDOWN4");
				raw_term rt128;
				rt128.neg = false;
				rt128.extype = raw_term::REL;
				rt128.e.push_back(e127);
				rt128.e.push_back(e1);
				rt128.e.push_back(e3);
				rt128.calc_arity(nullptr);
				raw_term rt130;
				rt130.neg = false;
				rt130.extype = raw_term::REL;
				rt130.e.push_back(e122);
				rt130.e.push_back(e1);
				rt130.e.push_back(e3);
				rt130.calc_arity(nullptr);
				sprawformtree ft129 = std::make_shared<raw_form_tree>(elem::NONE, rt130);
				raw_rule rr131;
				rr131.h.push_back(rt128);
				rr131.set_prft(ft129);
				elem e132;
				e132.type = elem::SYM;
				e132.e = d.get_lexeme("COUNTDOWN5");
				raw_term rt133;
				rt133.neg = false;
				rt133.extype = raw_term::REL;
				rt133.e.push_back(e132);
				rt133.e.push_back(e1);
				rt133.e.push_back(e3);
				rt133.calc_arity(nullptr);
				raw_term rt135;
				rt135.neg = false;
				rt135.extype = raw_term::REL;
				rt135.e.push_back(e127);
				rt135.e.push_back(e1);
				rt135.e.push_back(e3);
				rt135.calc_arity(nullptr);
				sprawformtree ft134 = std::make_shared<raw_form_tree>(elem::NONE, rt135);
				raw_rule rr136;
				rr136.h.push_back(rt133);
				rr136.set_prft(ft134);
				elem e137;
				e137.type = elem::SYM;
				e137.e = d.get_lexeme("COUNTDOWN6");
				raw_term rt138;
				rt138.neg = false;
				rt138.extype = raw_term::REL;
				rt138.e.push_back(e137);
				rt138.e.push_back(e1);
				rt138.e.push_back(e3);
				rt138.calc_arity(nullptr);
				raw_term rt140;
				rt140.neg = false;
				rt140.extype = raw_term::REL;
				rt140.e.push_back(e132);
				rt140.e.push_back(e1);
				rt140.e.push_back(e3);
				rt140.calc_arity(nullptr);
				sprawformtree ft139 = std::make_shared<raw_form_tree>(elem::NONE, rt140);
				raw_rule rr141;
				rr141.h.push_back(rt138);
				rr141.set_prft(ft139);
				raw_term rt142;
				rt142.neg = false;
				rt142.extype = raw_term::REL;
				rt142.e.push_back(e44);
				rt142.e.push_back(e1);
				rt142.e.push_back(e3);
				rt142.calc_arity(nullptr);
				raw_term rt145;
				rt145.neg = false;
				rt145.extype = raw_term::REL;
				rt145.e.push_back(e132);
				rt145.e.push_back(e1);
				rt145.e.push_back(e3);
				rt145.calc_arity(nullptr);
				sprawformtree ft144 = std::make_shared<raw_form_tree>(elem::NONE, rt145);
				raw_term rt148;
				rt148.neg = false;
				rt148.extype = raw_term::REL;
				rt148.e.push_back(e137);
				rt148.e.push_back(e1);
				rt148.e.push_back(e3);
				rt148.calc_arity(nullptr);
				sprawformtree ft147 = std::make_shared<raw_form_tree>(elem::NONE, rt148);
				sprawformtree ft146 = std::make_shared<raw_form_tree>(elem::NOT, ft147);
				sprawformtree ft143 = std::make_shared<raw_form_tree>(elem::AND, ft144, ft146);
				raw_rule rr149;
				rr149.h.push_back(rt142);
				rr149.set_prft(ft143);
				elem e150;
				e150.type = elem::SYM;
				e150.e = d.get_lexeme("DOMAIN");
				raw_term rt151;
				rt151.neg = false;
				rt151.extype = raw_term::REL;
				rt151.e.push_back(e150);
				rt151.e.push_back(e1);
				rt151.e.push_back(e59);
				rt151.e.push_back(e3);
				rt151.calc_arity(nullptr);
				elem &e153 = domain_sym;
				elem e154;
				e154.type = elem::VAR;
				e154.e = d.get_lexeme("?w");
				raw_term rt155;
				rt155.neg = false;
				rt155.extype = raw_term::REL;
				rt155.e.push_back(e153);
				rt155.e.push_back(e1);
				rt155.e.push_back(e154);
				rt155.e.push_back(e59);
				rt155.e.push_back(e47);
				rt155.e.push_back(e3);
				rt155.calc_arity(nullptr);
				sprawformtree ft152 = std::make_shared<raw_form_tree>(elem::NONE, rt155);
				raw_rule rr156;
				rr156.h.push_back(rt151);
				rr156.set_prft(ft152);
				elem e157;
				e157.type = elem::SYM;
				e157.e = d.get_lexeme("LIST");
				raw_term rt158;
				rt158.neg = false;
				rt158.extype = raw_term::REL;
				rt158.e.push_back(e157);
				rt158.e.push_back(e1);
				rt158.e.push_back(e2);
				rt158.e.push_back(e3);
				rt158.calc_arity(nullptr);
				raw_term rt160;
				rt160.neg = false;
				rt160.extype = raw_term::REL;
				rt160.e.push_back(e153);
				rt160.e.push_back(e1);
				rt160.e.push_back(e2);
				rt160.e.push_back(e3);
				rt160.calc_arity(nullptr);
				sprawformtree ft159 = std::make_shared<raw_form_tree>(elem::NONE, rt160);
				raw_rule rr161;
				rr161.h.push_back(rt158);
				rr161.set_prft(ft159);
				elem e162;
				e162.type = elem::VAR;
				e162.e = d.get_lexeme("?a");
				raw_term rt163;
				rt163.neg = false;
				rt163.extype = raw_term::REL;
				rt163.e.push_back(e157);
				rt163.e.push_back(e1);
				rt163.e.push_back(e2);
				rt163.e.push_back(e162);
				rt163.e.push_back(e3);
				rt163.calc_arity(nullptr);
				elem e166;
				e166.type = elem::VAR;
				e166.e = d.get_lexeme("?rst");
				raw_term rt167;
				rt167.neg = false;
				rt167.extype = raw_term::REL;
				rt167.e.push_back(e153);
				rt167.e.push_back(e1);
				rt167.e.push_back(e2);
				rt167.e.push_back(e162);
				rt167.e.push_back(e166);
				rt167.e.push_back(e3);
				rt167.calc_arity(nullptr);
				sprawformtree ft165 = std::make_shared<raw_form_tree>(elem::NONE, rt167);
				raw_term rt169;
				rt169.neg = false;
				rt169.extype = raw_term::REL;
				rt169.e.push_back(e157);
				rt169.e.push_back(e1);
				rt169.e.push_back(e166);
				rt169.e.push_back(e3);
				rt169.calc_arity(nullptr);
				sprawformtree ft168 = std::make_shared<raw_form_tree>(elem::NONE, rt169);
				sprawformtree ft164 = std::make_shared<raw_form_tree>(elem::AND, ft165, ft168);
				raw_rule rr170;
				rr170.h.push_back(rt163);
				rr170.set_prft(ft164);
				raw_term rt171;
				rt171.neg = false;
				rt171.extype = raw_term::REL;
				rt171.e.push_back(e157);
				rt171.e.push_back(e1);
				rt171.e.push_back(e2);
				rt171.e.push_back(e162);
				rt171.e.push_back(e39);
				rt171.e.push_back(e3);
				rt171.calc_arity(nullptr);
				raw_term rt174;
				rt174.neg = false;
				rt174.extype = raw_term::REL;
				rt174.e.push_back(e153);
				rt174.e.push_back(e1);
				rt174.e.push_back(e2);
				rt174.e.push_back(e162);
				rt174.e.push_back(e166);
				rt174.e.push_back(e3);
				rt174.calc_arity(nullptr);
				sprawformtree ft173 = std::make_shared<raw_form_tree>(elem::NONE, rt174);
				raw_term rt176;
				rt176.neg = false;
				rt176.extype = raw_term::REL;
				rt176.e.push_back(e157);
				rt176.e.push_back(e1);
				rt176.e.push_back(e166);
				rt176.e.push_back(e39);
				rt176.e.push_back(e3);
				rt176.calc_arity(nullptr);
				sprawformtree ft175 = std::make_shared<raw_form_tree>(elem::NONE, rt176);
				sprawformtree ft172 = std::make_shared<raw_form_tree>(elem::AND, ft173, ft175);
				raw_rule rr177;
				rr177.h.push_back(rt171);
				rr177.set_prft(ft172);
				elem e178;
				e178.type = elem::VAR;
				e178.e = d.get_lexeme("?c");
				raw_term rt179;
				rt179.neg = false;
				rt179.extype = raw_term::REL;
				rt179.e.push_back(e157);
				rt179.e.push_back(e1);
				rt179.e.push_back(e2);
				rt179.e.push_back(e162);
				rt179.e.push_back(e39);
				rt179.e.push_back(e178);
				rt179.e.push_back(e3);
				rt179.calc_arity(nullptr);
				raw_term rt182;
				rt182.neg = false;
				rt182.extype = raw_term::REL;
				rt182.e.push_back(e153);
				rt182.e.push_back(e1);
				rt182.e.push_back(e2);
				rt182.e.push_back(e162);
				rt182.e.push_back(e166);
				rt182.e.push_back(e3);
				rt182.calc_arity(nullptr);
				sprawformtree ft181 = std::make_shared<raw_form_tree>(elem::NONE, rt182);
				raw_term rt184;
				rt184.neg = false;
				rt184.extype = raw_term::REL;
				rt184.e.push_back(e157);
				rt184.e.push_back(e1);
				rt184.e.push_back(e166);
				rt184.e.push_back(e39);
				rt184.e.push_back(e178);
				rt184.e.push_back(e3);
				rt184.calc_arity(nullptr);
				sprawformtree ft183 = std::make_shared<raw_form_tree>(elem::NONE, rt184);
				sprawformtree ft180 = std::make_shared<raw_form_tree>(elem::AND, ft181, ft183);
				raw_rule rr185;
				rr185.h.push_back(rt179);
				rr185.set_prft(ft180);
				elem e186;
				e186.type = elem::VAR;
				e186.e = d.get_lexeme("?d");
				raw_term rt187;
				rt187.neg = false;
				rt187.extype = raw_term::REL;
				rt187.e.push_back(e157);
				rt187.e.push_back(e1);
				rt187.e.push_back(e2);
				rt187.e.push_back(e162);
				rt187.e.push_back(e39);
				rt187.e.push_back(e178);
				rt187.e.push_back(e186);
				rt187.e.push_back(e3);
				rt187.calc_arity(nullptr);
				raw_term rt190;
				rt190.neg = false;
				rt190.extype = raw_term::REL;
				rt190.e.push_back(e153);
				rt190.e.push_back(e1);
				rt190.e.push_back(e2);
				rt190.e.push_back(e162);
				rt190.e.push_back(e166);
				rt190.e.push_back(e3);
				rt190.calc_arity(nullptr);
				sprawformtree ft189 = std::make_shared<raw_form_tree>(elem::NONE, rt190);
				raw_term rt192;
				rt192.neg = false;
				rt192.extype = raw_term::REL;
				rt192.e.push_back(e157);
				rt192.e.push_back(e1);
				rt192.e.push_back(e166);
				rt192.e.push_back(e39);
				rt192.e.push_back(e178);
				rt192.e.push_back(e186);
				rt192.e.push_back(e3);
				rt192.calc_arity(nullptr);
				sprawformtree ft191 = std::make_shared<raw_form_tree>(elem::NONE, rt192);
				sprawformtree ft188 = std::make_shared<raw_form_tree>(elem::AND, ft189, ft191);
				raw_rule rr193;
				rr193.h.push_back(rt187);
				rr193.set_prft(ft188);
				elem e194;
				e194.type = elem::SYM;
				e194.e = d.get_lexeme("DO_RAPPEND0");
				elem e195;
				e195.type = elem::VAR;
				e195.e = d.get_lexeme("?xs");
				elem e196;
				e196.type = elem::VAR;
				e196.e = d.get_lexeme("?ys");
				raw_term rt197;
				rt197.neg = false;
				rt197.extype = raw_term::REL;
				rt197.e.push_back(e194);
				rt197.e.push_back(e1);
				rt197.e.push_back(e195);
				rt197.e.push_back(e196);
				rt197.e.push_back(e195);
				rt197.e.push_back(e196);
				rt197.e.push_back(e3);
				rt197.calc_arity(nullptr);
				elem e200;
				e200.type = elem::SYM;
				e200.e = d.get_lexeme("DO_RAPPEND");
				raw_term rt201;
				rt201.neg = false;
				rt201.extype = raw_term::REL;
				rt201.e.push_back(e200);
				rt201.e.push_back(e1);
				rt201.e.push_back(e195);
				rt201.e.push_back(e196);
				rt201.e.push_back(e3);
				rt201.calc_arity(nullptr);
				sprawformtree ft199 = std::make_shared<raw_form_tree>(elem::NONE, rt201);
				elem e205;
				e205.type = elem::VAR;
				e205.e = d.get_lexeme("?cs");
				sprawformtree ft204 = std::make_shared<raw_form_tree>(elem::VAR, e205);
				elem e207;
				e207.type = elem::SYM;
				e207.e = d.get_lexeme("RAPPEND");
				raw_term rt208;
				rt208.neg = false;
				rt208.extype = raw_term::REL;
				rt208.e.push_back(e207);
				rt208.e.push_back(e1);
				rt208.e.push_back(e205);
				rt208.e.push_back(e195);
				rt208.e.push_back(e196);
				rt208.e.push_back(e3);
				rt208.calc_arity(nullptr);
				sprawformtree ft206 = std::make_shared<raw_form_tree>(elem::NONE, rt208);
				sprawformtree ft203 = std::make_shared<raw_form_tree>(elem::EXISTS, ft204, ft206);
				sprawformtree ft202 = std::make_shared<raw_form_tree>(elem::NOT, ft203);
				sprawformtree ft198 = std::make_shared<raw_form_tree>(elem::AND, ft199, ft202);
				raw_rule rr209;
				rr209.h.push_back(rt197);
				rr209.set_prft(ft198);
				elem e210;
				e210.type = elem::VAR;
				e210.e = d.get_lexeme("?oxs");
				elem e211;
				e211.type = elem::VAR;
				e211.e = d.get_lexeme("?oys");
				elem e212;
				e212.type = elem::VAR;
				e212.e = d.get_lexeme("?xs_tl");
				raw_term rt213;
				rt213.neg = false;
				rt213.extype = raw_term::REL;
				rt213.e.push_back(e194);
				rt213.e.push_back(e1);
				rt213.e.push_back(e210);
				rt213.e.push_back(e211);
				rt213.e.push_back(e212);
				rt213.e.push_back(e196);
				rt213.e.push_back(e3);
				rt213.calc_arity(nullptr);
				elem e218;
				e218.type = elem::VAR;
				e218.e = d.get_lexeme("?ys_tl");
				raw_term rt219;
				rt219.neg = false;
				rt219.extype = raw_term::REL;
				rt219.e.push_back(e194);
				rt219.e.push_back(e1);
				rt219.e.push_back(e210);
				rt219.e.push_back(e211);
				rt219.e.push_back(e195);
				rt219.e.push_back(e218);
				rt219.e.push_back(e3);
				rt219.calc_arity(nullptr);
				sprawformtree ft217 = std::make_shared<raw_form_tree>(elem::NONE, rt219);
				elem e221;
				e221.type = elem::VAR;
				e221.e = d.get_lexeme("?xs_hd");
				raw_term rt222;
				rt222.neg = false;
				rt222.extype = raw_term::REL;
				rt222.e.push_back(e153);
				rt222.e.push_back(e1);
				rt222.e.push_back(e195);
				rt222.e.push_back(e221);
				rt222.e.push_back(e212);
				rt222.e.push_back(e3);
				rt222.calc_arity(nullptr);
				sprawformtree ft220 = std::make_shared<raw_form_tree>(elem::NONE, rt222);
				sprawformtree ft216 = std::make_shared<raw_form_tree>(elem::AND, ft217, ft220);
				raw_term rt224;
				rt224.neg = false;
				rt224.extype = raw_term::REL;
				rt224.e.push_back(e153);
				rt224.e.push_back(e1);
				rt224.e.push_back(e196);
				rt224.e.push_back(e221);
				rt224.e.push_back(e218);
				rt224.e.push_back(e3);
				rt224.calc_arity(nullptr);
				sprawformtree ft223 = std::make_shared<raw_form_tree>(elem::NONE, rt224);
				sprawformtree ft215 = std::make_shared<raw_form_tree>(elem::AND, ft216, ft223);
				sprawformtree ft227 = std::make_shared<raw_form_tree>(elem::VAR, e205);
				raw_term rt229;
				rt229.neg = false;
				rt229.extype = raw_term::REL;
				rt229.e.push_back(e207);
				rt229.e.push_back(e1);
				rt229.e.push_back(e205);
				rt229.e.push_back(e210);
				rt229.e.push_back(e211);
				rt229.e.push_back(e3);
				rt229.calc_arity(nullptr);
				sprawformtree ft228 = std::make_shared<raw_form_tree>(elem::NONE, rt229);
				sprawformtree ft226 = std::make_shared<raw_form_tree>(elem::EXISTS, ft227, ft228);
				sprawformtree ft225 = std::make_shared<raw_form_tree>(elem::NOT, ft226);
				sprawformtree ft214 = std::make_shared<raw_form_tree>(elem::AND, ft215, ft225);
				raw_rule rr230;
				rr230.h.push_back(rt213);
				rr230.set_prft(ft214);
				elem e231;
				e231.type = elem::VAR;
				e231.e = d.get_lexeme("?zs");
				raw_term rt232;
				rt232.neg = false;
				rt232.extype = raw_term::REL;
				rt232.e.push_back(e207);
				rt232.e.push_back(e1);
				rt232.e.push_back(e231);
				rt232.e.push_back(e195);
				rt232.e.push_back(e196);
				rt232.e.push_back(e3);
				rt232.calc_arity(nullptr);
				elem e236;
				e236.type = elem::VAR;
				e236.e = d.get_lexeme("?as");
				raw_term rt237;
				rt237.neg = false;
				rt237.extype = raw_term::REL;
				rt237.e.push_back(e194);
				rt237.e.push_back(e1);
				rt237.e.push_back(e195);
				rt237.e.push_back(e196);
				rt237.e.push_back(e236);
				rt237.e.push_back(e231);
				rt237.e.push_back(e3);
				rt237.calc_arity(nullptr);
				sprawformtree ft235 = std::make_shared<raw_form_tree>(elem::NONE, rt237);
				raw_term rt239;
				rt239.neg = false;
				rt239.extype = raw_term::REL;
				rt239.e.push_back(e153);
				rt239.e.push_back(e1);
				rt239.e.push_back(e236);
				rt239.e.push_back(e3);
				rt239.calc_arity(nullptr);
				sprawformtree ft238 = std::make_shared<raw_form_tree>(elem::NONE, rt239);
				sprawformtree ft234 = std::make_shared<raw_form_tree>(elem::AND, ft235, ft238);
				sprawformtree ft242 = std::make_shared<raw_form_tree>(elem::VAR, e205);
				raw_term rt244;
				rt244.neg = false;
				rt244.extype = raw_term::REL;
				rt244.e.push_back(e207);
				rt244.e.push_back(e1);
				rt244.e.push_back(e205);
				rt244.e.push_back(e195);
				rt244.e.push_back(e196);
				rt244.e.push_back(e3);
				rt244.calc_arity(nullptr);
				sprawformtree ft243 = std::make_shared<raw_form_tree>(elem::NONE, rt244);
				sprawformtree ft241 = std::make_shared<raw_form_tree>(elem::EXISTS, ft242, ft243);
				sprawformtree ft240 = std::make_shared<raw_form_tree>(elem::NOT, ft241);
				sprawformtree ft233 = std::make_shared<raw_form_tree>(elem::AND, ft234, ft240);
				raw_rule rr245;
				rr245.h.push_back(rt232);
				rr245.set_prft(ft233);
				raw_term rt246;
				rt246.neg = true;
				rt246.extype = raw_term::REL;
				rt246.e.push_back(e194);
				rt246.e.push_back(e1);
				rt246.e.push_back(e210);
				rt246.e.push_back(e211);
				rt246.e.push_back(e195);
				rt246.e.push_back(e196);
				rt246.e.push_back(e3);
				rt246.calc_arity(nullptr);
				raw_term rt248;
				rt248.neg = false;
				rt248.extype = raw_term::REL;
				rt248.e.push_back(e207);
				rt248.e.push_back(e1);
				rt248.e.push_back(e205);
				rt248.e.push_back(e210);
				rt248.e.push_back(e211);
				rt248.e.push_back(e3);
				rt248.calc_arity(nullptr);
				sprawformtree ft247 = std::make_shared<raw_form_tree>(elem::NONE, rt248);
				raw_rule rr249;
				rr249.h.push_back(rt246);
				rr249.set_prft(ft247);
				elem e250;
				e250.type = elem::SYM;
				e250.e = d.get_lexeme("DO_REVERSE");
				elem e251;
				e251.type = elem::VAR;
				e251.e = d.get_lexeme("?bs");
				raw_term rt252;
				rt252.neg = false;
				rt252.extype = raw_term::REL;
				rt252.e.push_back(e250);
				rt252.e.push_back(e1);
				rt252.e.push_back(e251);
				rt252.e.push_back(e236);
				rt252.e.push_back(e251);
				rt252.e.push_back(e3);
				rt252.calc_arity(nullptr);
				raw_term rt256;
				rt256.neg = false;
				rt256.extype = raw_term::REL;
				rt256.e.push_back(e250);
				rt256.e.push_back(e1);
				rt256.e.push_back(e251);
				rt256.e.push_back(e3);
				rt256.calc_arity(nullptr);
				sprawformtree ft255 = std::make_shared<raw_form_tree>(elem::NONE, rt256);
				raw_term rt258;
				rt258.neg = false;
				rt258.extype = raw_term::REL;
				rt258.e.push_back(e153);
				rt258.e.push_back(e1);
				rt258.e.push_back(e236);
				rt258.e.push_back(e3);
				rt258.calc_arity(nullptr);
				sprawformtree ft257 = std::make_shared<raw_form_tree>(elem::NONE, rt258);
				sprawformtree ft254 = std::make_shared<raw_form_tree>(elem::AND, ft255, ft257);
				sprawformtree ft261 = std::make_shared<raw_form_tree>(elem::VAR, e162);
				elem e263;
				e263.type = elem::SYM;
				e263.e = d.get_lexeme("REVERSE");
				raw_term rt264;
				rt264.neg = false;
				rt264.extype = raw_term::REL;
				rt264.e.push_back(e263);
				rt264.e.push_back(e1);
				rt264.e.push_back(e251);
				rt264.e.push_back(e162);
				rt264.e.push_back(e3);
				rt264.calc_arity(nullptr);
				sprawformtree ft262 = std::make_shared<raw_form_tree>(elem::NONE, rt264);
				sprawformtree ft260 = std::make_shared<raw_form_tree>(elem::EXISTS, ft261, ft262);
				sprawformtree ft259 = std::make_shared<raw_form_tree>(elem::NOT, ft260);
				sprawformtree ft253 = std::make_shared<raw_form_tree>(elem::AND, ft254, ft259);
				raw_rule rr265;
				rr265.h.push_back(rt252);
				rr265.set_prft(ft253);
				elem e266;
				e266.type = elem::VAR;
				e266.e = d.get_lexeme("?obs");
				raw_term rt267;
				rt267.neg = false;
				rt267.extype = raw_term::REL;
				rt267.e.push_back(e250);
				rt267.e.push_back(e1);
				rt267.e.push_back(e266);
				rt267.e.push_back(e236);
				rt267.e.push_back(e251);
				rt267.e.push_back(e3);
				rt267.calc_arity(nullptr);
				elem e272;
				e272.type = elem::VAR;
				e272.e = d.get_lexeme("?as_hd");
				elem e273;
				e273.type = elem::VAR;
				e273.e = d.get_lexeme("?as_tl");
				raw_term rt274;
				rt274.neg = false;
				rt274.extype = raw_term::REL;
				rt274.e.push_back(e153);
				rt274.e.push_back(e1);
				rt274.e.push_back(e236);
				rt274.e.push_back(e272);
				rt274.e.push_back(e273);
				rt274.e.push_back(e3);
				rt274.calc_arity(nullptr);
				sprawformtree ft271 = std::make_shared<raw_form_tree>(elem::NONE, rt274);
				elem e276;
				e276.type = elem::VAR;
				e276.e = d.get_lexeme("?nbs");
				raw_term rt277;
				rt277.neg = false;
				rt277.extype = raw_term::REL;
				rt277.e.push_back(e153);
				rt277.e.push_back(e1);
				rt277.e.push_back(e276);
				rt277.e.push_back(e272);
				rt277.e.push_back(e251);
				rt277.e.push_back(e3);
				rt277.calc_arity(nullptr);
				sprawformtree ft275 = std::make_shared<raw_form_tree>(elem::NONE, rt277);
				sprawformtree ft270 = std::make_shared<raw_form_tree>(elem::AND, ft271, ft275);
				raw_term rt279;
				rt279.neg = false;
				rt279.extype = raw_term::REL;
				rt279.e.push_back(e250);
				rt279.e.push_back(e1);
				rt279.e.push_back(e266);
				rt279.e.push_back(e273);
				rt279.e.push_back(e276);
				rt279.e.push_back(e3);
				rt279.calc_arity(nullptr);
				sprawformtree ft278 = std::make_shared<raw_form_tree>(elem::NONE, rt279);
				sprawformtree ft269 = std::make_shared<raw_form_tree>(elem::AND, ft270, ft278);
				sprawformtree ft282 = std::make_shared<raw_form_tree>(elem::VAR, e162);
				raw_term rt284;
				rt284.neg = false;
				rt284.extype = raw_term::REL;
				rt284.e.push_back(e263);
				rt284.e.push_back(e1);
				rt284.e.push_back(e266);
				rt284.e.push_back(e162);
				rt284.e.push_back(e3);
				rt284.calc_arity(nullptr);
				sprawformtree ft283 = std::make_shared<raw_form_tree>(elem::NONE, rt284);
				sprawformtree ft281 = std::make_shared<raw_form_tree>(elem::EXISTS, ft282, ft283);
				sprawformtree ft280 = std::make_shared<raw_form_tree>(elem::NOT, ft281);
				sprawformtree ft268 = std::make_shared<raw_form_tree>(elem::AND, ft269, ft280);
				raw_rule rr285;
				rr285.h.push_back(rt267);
				rr285.set_prft(ft268);
				raw_term rt286;
				rt286.neg = false;
				rt286.extype = raw_term::REL;
				rt286.e.push_back(e263);
				rt286.e.push_back(e1);
				rt286.e.push_back(e266);
				rt286.e.push_back(e236);
				rt286.e.push_back(e3);
				rt286.calc_arity(nullptr);
				raw_term rt290;
				rt290.neg = false;
				rt290.extype = raw_term::REL;
				rt290.e.push_back(e250);
				rt290.e.push_back(e1);
				rt290.e.push_back(e266);
				rt290.e.push_back(e236);
				rt290.e.push_back(e251);
				rt290.e.push_back(e3);
				rt290.calc_arity(nullptr);
				sprawformtree ft289 = std::make_shared<raw_form_tree>(elem::NONE, rt290);
				raw_term rt292;
				rt292.neg = false;
				rt292.extype = raw_term::REL;
				rt292.e.push_back(e153);
				rt292.e.push_back(e1);
				rt292.e.push_back(e251);
				rt292.e.push_back(e3);
				rt292.calc_arity(nullptr);
				sprawformtree ft291 = std::make_shared<raw_form_tree>(elem::NONE, rt292);
				sprawformtree ft288 = std::make_shared<raw_form_tree>(elem::AND, ft289, ft291);
				sprawformtree ft295 = std::make_shared<raw_form_tree>(elem::VAR, e162);
				raw_term rt297;
				rt297.neg = false;
				rt297.extype = raw_term::REL;
				rt297.e.push_back(e263);
				rt297.e.push_back(e1);
				rt297.e.push_back(e266);
				rt297.e.push_back(e162);
				rt297.e.push_back(e3);
				rt297.calc_arity(nullptr);
				sprawformtree ft296 = std::make_shared<raw_form_tree>(elem::NONE, rt297);
				sprawformtree ft294 = std::make_shared<raw_form_tree>(elem::EXISTS, ft295, ft296);
				sprawformtree ft293 = std::make_shared<raw_form_tree>(elem::NOT, ft294);
				sprawformtree ft287 = std::make_shared<raw_form_tree>(elem::AND, ft288, ft293);
				raw_rule rr298;
				rr298.h.push_back(rt286);
				rr298.set_prft(ft287);
				raw_term rt299;
				rt299.neg = true;
				rt299.extype = raw_term::REL;
				rt299.e.push_back(e250);
				rt299.e.push_back(e1);
				rt299.e.push_back(e266);
				rt299.e.push_back(e236);
				rt299.e.push_back(e251);
				rt299.e.push_back(e3);
				rt299.calc_arity(nullptr);
				raw_term rt301;
				rt301.neg = false;
				rt301.extype = raw_term::REL;
				rt301.e.push_back(e263);
				rt301.e.push_back(e1);
				rt301.e.push_back(e266);
				rt301.e.push_back(e205);
				rt301.e.push_back(e3);
				rt301.calc_arity(nullptr);
				sprawformtree ft300 = std::make_shared<raw_form_tree>(elem::NONE, rt301);
				raw_rule rr302;
				rr302.h.push_back(rt299);
				rr302.set_prft(ft300);
				elem e303;
				e303.type = elem::SYM;
				e303.e = d.get_lexeme("ASSOC0");
				raw_term rt304;
				rt304.neg = false;
				rt304.extype = raw_term::REL;
				rt304.e.push_back(e303);
				rt304.e.push_back(e1);
				rt304.e.push_back(e195);
				rt304.e.push_back(e196);
				rt304.e.push_back(e195);
				rt304.e.push_back(e196);
				rt304.e.push_back(e59);
				rt304.e.push_back(e3);
				rt304.calc_arity(nullptr);
				elem e308;
				e308.type = elem::SYM;
				e308.e = d.get_lexeme("ASSOC");
				raw_term rt309;
				rt309.neg = false;
				rt309.extype = raw_term::REL;
				rt309.e.push_back(e308);
				rt309.e.push_back(e1);
				rt309.e.push_back(e195);
				rt309.e.push_back(e196);
				rt309.e.push_back(e59);
				rt309.e.push_back(e3);
				rt309.calc_arity(nullptr);
				sprawformtree ft307 = std::make_shared<raw_form_tree>(elem::NONE, rt309);
				sprawformtree ft312 = std::make_shared<raw_form_tree>(elem::VAR, e47);
				raw_term rt314;
				rt314.neg = false;
				rt314.extype = raw_term::REL;
				rt314.e.push_back(e308);
				rt314.e.push_back(e1);
				rt314.e.push_back(e195);
				rt314.e.push_back(e196);
				rt314.e.push_back(e59);
				rt314.e.push_back(e47);
				rt314.e.push_back(e3);
				rt314.calc_arity(nullptr);
				sprawformtree ft313 = std::make_shared<raw_form_tree>(elem::NONE, rt314);
				sprawformtree ft311 = std::make_shared<raw_form_tree>(elem::EXISTS, ft312, ft313);
				sprawformtree ft310 = std::make_shared<raw_form_tree>(elem::NOT, ft311);
				sprawformtree ft306 = std::make_shared<raw_form_tree>(elem::AND, ft307, ft310);
				elem e317;
				e317.type = elem::SYM;
				e317.e = d.get_lexeme("NO_ASSOC");
				raw_term rt318;
				rt318.neg = false;
				rt318.extype = raw_term::REL;
				rt318.e.push_back(e317);
				rt318.e.push_back(e1);
				rt318.e.push_back(e195);
				rt318.e.push_back(e196);
				rt318.e.push_back(e59);
				rt318.e.push_back(e3);
				rt318.calc_arity(nullptr);
				sprawformtree ft316 = std::make_shared<raw_form_tree>(elem::NONE, rt318);
				sprawformtree ft315 = std::make_shared<raw_form_tree>(elem::NOT, ft316);
				sprawformtree ft305 = std::make_shared<raw_form_tree>(elem::AND, ft306, ft315);
				raw_rule rr319;
				rr319.h.push_back(rt304);
				rr319.set_prft(ft305);
				elem e320;
				e320.type = elem::VAR;
				e320.e = d.get_lexeme("?yn");
				raw_term rt321;
				rt321.neg = false;
				rt321.extype = raw_term::REL;
				rt321.e.push_back(e303);
				rt321.e.push_back(e1);
				rt321.e.push_back(e210);
				rt321.e.push_back(e211);
				rt321.e.push_back(e212);
				rt321.e.push_back(e218);
				rt321.e.push_back(e59);
				rt321.e.push_back(e320);
				rt321.e.push_back(e3);
				rt321.calc_arity(nullptr);
				raw_term rt327;
				rt327.neg = false;
				rt327.extype = raw_term::REL;
				rt327.e.push_back(e153);
				rt327.e.push_back(e1);
				rt327.e.push_back(e195);
				rt327.e.push_back(e59);
				rt327.e.push_back(e212);
				rt327.e.push_back(e3);
				rt327.calc_arity(nullptr);
				sprawformtree ft326 = std::make_shared<raw_form_tree>(elem::NONE, rt327);
				raw_term rt329;
				rt329.neg = false;
				rt329.extype = raw_term::REL;
				rt329.e.push_back(e153);
				rt329.e.push_back(e1);
				rt329.e.push_back(e196);
				rt329.e.push_back(e320);
				rt329.e.push_back(e218);
				rt329.e.push_back(e3);
				rt329.calc_arity(nullptr);
				sprawformtree ft328 = std::make_shared<raw_form_tree>(elem::NONE, rt329);
				sprawformtree ft325 = std::make_shared<raw_form_tree>(elem::AND, ft326, ft328);
				raw_term rt331;
				rt331.neg = false;
				rt331.extype = raw_term::REL;
				rt331.e.push_back(e303);
				rt331.e.push_back(e1);
				rt331.e.push_back(e210);
				rt331.e.push_back(e211);
				rt331.e.push_back(e195);
				rt331.e.push_back(e196);
				rt331.e.push_back(e59);
				rt331.e.push_back(e3);
				rt331.calc_arity(nullptr);
				sprawformtree ft330 = std::make_shared<raw_form_tree>(elem::NONE, rt331);
				sprawformtree ft324 = std::make_shared<raw_form_tree>(elem::AND, ft325, ft330);
				sprawformtree ft334 = std::make_shared<raw_form_tree>(elem::VAR, e47);
				raw_term rt336;
				rt336.neg = false;
				rt336.extype = raw_term::REL;
				rt336.e.push_back(e308);
				rt336.e.push_back(e1);
				rt336.e.push_back(e210);
				rt336.e.push_back(e211);
				rt336.e.push_back(e59);
				rt336.e.push_back(e47);
				rt336.e.push_back(e3);
				rt336.calc_arity(nullptr);
				sprawformtree ft335 = std::make_shared<raw_form_tree>(elem::NONE, rt336);
				sprawformtree ft333 = std::make_shared<raw_form_tree>(elem::EXISTS, ft334, ft335);
				sprawformtree ft332 = std::make_shared<raw_form_tree>(elem::NOT, ft333);
				sprawformtree ft323 = std::make_shared<raw_form_tree>(elem::AND, ft324, ft332);
				raw_term rt339;
				rt339.neg = false;
				rt339.extype = raw_term::REL;
				rt339.e.push_back(e317);
				rt339.e.push_back(e1);
				rt339.e.push_back(e210);
				rt339.e.push_back(e211);
				rt339.e.push_back(e59);
				rt339.e.push_back(e3);
				rt339.calc_arity(nullptr);
				sprawformtree ft338 = std::make_shared<raw_form_tree>(elem::NONE, rt339);
				sprawformtree ft337 = std::make_shared<raw_form_tree>(elem::NOT, ft338);
				sprawformtree ft322 = std::make_shared<raw_form_tree>(elem::AND, ft323, ft337);
				raw_rule rr340;
				rr340.h.push_back(rt321);
				rr340.set_prft(ft322);
				raw_term rt341;
				rt341.neg = false;
				rt341.extype = raw_term::REL;
				rt341.e.push_back(e317);
				rt341.e.push_back(e1);
				rt341.e.push_back(e210);
				rt341.e.push_back(e211);
				rt341.e.push_back(e59);
				rt341.e.push_back(e3);
				rt341.calc_arity(nullptr);
				raw_term rt347;
				rt347.neg = false;
				rt347.extype = raw_term::REL;
				rt347.e.push_back(e153);
				rt347.e.push_back(e1);
				rt347.e.push_back(e195);
				rt347.e.push_back(e59);
				rt347.e.push_back(e212);
				rt347.e.push_back(e3);
				rt347.calc_arity(nullptr);
				sprawformtree ft346 = std::make_shared<raw_form_tree>(elem::NONE, rt347);
				raw_term rt349;
				rt349.neg = false;
				rt349.extype = raw_term::REL;
				rt349.e.push_back(e153);
				rt349.e.push_back(e1);
				rt349.e.push_back(e196);
				rt349.e.push_back(e320);
				rt349.e.push_back(e218);
				rt349.e.push_back(e3);
				rt349.calc_arity(nullptr);
				sprawformtree ft348 = std::make_shared<raw_form_tree>(elem::NONE, rt349);
				sprawformtree ft345 = std::make_shared<raw_form_tree>(elem::AND, ft346, ft348);
				raw_term rt351;
				rt351.neg = false;
				rt351.extype = raw_term::REL;
				rt351.e.push_back(e303);
				rt351.e.push_back(e1);
				rt351.e.push_back(e210);
				rt351.e.push_back(e211);
				rt351.e.push_back(e195);
				rt351.e.push_back(e196);
				rt351.e.push_back(e59);
				rt351.e.push_back(e47);
				rt351.e.push_back(e3);
				rt351.calc_arity(nullptr);
				sprawformtree ft350 = std::make_shared<raw_form_tree>(elem::NONE, rt351);
				sprawformtree ft344 = std::make_shared<raw_form_tree>(elem::AND, ft345, ft350);
				sprawformtree ft354 = std::make_shared<raw_form_tree>(elem::VAR, e47);
				raw_term rt356;
				rt356.neg = false;
				rt356.extype = raw_term::REL;
				rt356.e.push_back(e308);
				rt356.e.push_back(e1);
				rt356.e.push_back(e210);
				rt356.e.push_back(e211);
				rt356.e.push_back(e59);
				rt356.e.push_back(e47);
				rt356.e.push_back(e3);
				rt356.calc_arity(nullptr);
				sprawformtree ft355 = std::make_shared<raw_form_tree>(elem::NONE, rt356);
				sprawformtree ft353 = std::make_shared<raw_form_tree>(elem::EXISTS, ft354, ft355);
				sprawformtree ft352 = std::make_shared<raw_form_tree>(elem::NOT, ft353);
				sprawformtree ft343 = std::make_shared<raw_form_tree>(elem::AND, ft344, ft352);
				raw_term rt359;
				rt359.neg = false;
				rt359.extype = raw_term::REL;
				rt359.e.push_back(e317);
				rt359.e.push_back(e1);
				rt359.e.push_back(e210);
				rt359.e.push_back(e211);
				rt359.e.push_back(e59);
				rt359.e.push_back(e3);
				rt359.calc_arity(nullptr);
				sprawformtree ft358 = std::make_shared<raw_form_tree>(elem::NONE, rt359);
				sprawformtree ft357 = std::make_shared<raw_form_tree>(elem::NOT, ft358);
				sprawformtree ft342 = std::make_shared<raw_form_tree>(elem::AND, ft343, ft357);
				raw_rule rr360;
				rr360.h.push_back(rt341);
				rr360.set_prft(ft342);
				raw_term rt361;
				rt361.neg = false;
				rt361.extype = raw_term::REL;
				rt361.e.push_back(e303);
				rt361.e.push_back(e1);
				rt361.e.push_back(e210);
				rt361.e.push_back(e211);
				rt361.e.push_back(e212);
				rt361.e.push_back(e218);
				rt361.e.push_back(e59);
				rt361.e.push_back(e3);
				rt361.calc_arity(nullptr);
				elem e368;
				e368.type = elem::VAR;
				e368.e = d.get_lexeme("?xn");
				raw_term rt369;
				rt369.neg = false;
				rt369.extype = raw_term::REL;
				rt369.e.push_back(e153);
				rt369.e.push_back(e1);
				rt369.e.push_back(e195);
				rt369.e.push_back(e368);
				rt369.e.push_back(e212);
				rt369.e.push_back(e3);
				rt369.calc_arity(nullptr);
				sprawformtree ft367 = std::make_shared<raw_form_tree>(elem::NONE, rt369);
				raw_term rt371;
				rt371.neg = false;
				rt371.extype = raw_term::REL;
				rt371.e.push_back(e153);
				rt371.e.push_back(e1);
				rt371.e.push_back(e196);
				rt371.e.push_back(e320);
				rt371.e.push_back(e218);
				rt371.e.push_back(e3);
				rt371.calc_arity(nullptr);
				sprawformtree ft370 = std::make_shared<raw_form_tree>(elem::NONE, rt371);
				sprawformtree ft366 = std::make_shared<raw_form_tree>(elem::AND, ft367, ft370);
				raw_term rt373;
				rt373.neg = false;
				rt373.extype = raw_term::REL;
				rt373.e.push_back(e303);
				rt373.e.push_back(e1);
				rt373.e.push_back(e210);
				rt373.e.push_back(e211);
				rt373.e.push_back(e195);
				rt373.e.push_back(e196);
				rt373.e.push_back(e59);
				rt373.e.push_back(e3);
				rt373.calc_arity(nullptr);
				sprawformtree ft372 = std::make_shared<raw_form_tree>(elem::NONE, rt373);
				sprawformtree ft365 = std::make_shared<raw_form_tree>(elem::AND, ft366, ft372);
				raw_term rt376;
				rt376.neg = false;
				rt376.extype = raw_term::EQ;
				rt376.e.push_back(e368);
				rt376.e.push_back(e109);
				rt376.e.push_back(e59);
				rt376.calc_arity(nullptr);
				sprawformtree ft375 = std::make_shared<raw_form_tree>(elem::NONE, rt376);
				sprawformtree ft374 = std::make_shared<raw_form_tree>(elem::NOT, ft375);
				sprawformtree ft364 = std::make_shared<raw_form_tree>(elem::AND, ft365, ft374);
				sprawformtree ft379 = std::make_shared<raw_form_tree>(elem::VAR, e47);
				raw_term rt381;
				rt381.neg = false;
				rt381.extype = raw_term::REL;
				rt381.e.push_back(e308);
				rt381.e.push_back(e1);
				rt381.e.push_back(e210);
				rt381.e.push_back(e211);
				rt381.e.push_back(e59);
				rt381.e.push_back(e47);
				rt381.e.push_back(e3);
				rt381.calc_arity(nullptr);
				sprawformtree ft380 = std::make_shared<raw_form_tree>(elem::NONE, rt381);
				sprawformtree ft378 = std::make_shared<raw_form_tree>(elem::EXISTS, ft379, ft380);
				sprawformtree ft377 = std::make_shared<raw_form_tree>(elem::NOT, ft378);
				sprawformtree ft363 = std::make_shared<raw_form_tree>(elem::AND, ft364, ft377);
				raw_term rt384;
				rt384.neg = false;
				rt384.extype = raw_term::REL;
				rt384.e.push_back(e317);
				rt384.e.push_back(e1);
				rt384.e.push_back(e210);
				rt384.e.push_back(e211);
				rt384.e.push_back(e59);
				rt384.e.push_back(e3);
				rt384.calc_arity(nullptr);
				sprawformtree ft383 = std::make_shared<raw_form_tree>(elem::NONE, rt384);
				sprawformtree ft382 = std::make_shared<raw_form_tree>(elem::NOT, ft383);
				sprawformtree ft362 = std::make_shared<raw_form_tree>(elem::AND, ft363, ft382);
				raw_rule rr385;
				rr385.h.push_back(rt361);
				rr385.set_prft(ft362);
				raw_term rt386;
				rt386.neg = false;
				rt386.extype = raw_term::REL;
				rt386.e.push_back(e303);
				rt386.e.push_back(e1);
				rt386.e.push_back(e210);
				rt386.e.push_back(e211);
				rt386.e.push_back(e212);
				rt386.e.push_back(e218);
				rt386.e.push_back(e59);
				rt386.e.push_back(e47);
				rt386.e.push_back(e3);
				rt386.calc_arity(nullptr);
				raw_term rt393;
				rt393.neg = false;
				rt393.extype = raw_term::REL;
				rt393.e.push_back(e153);
				rt393.e.push_back(e1);
				rt393.e.push_back(e195);
				rt393.e.push_back(e368);
				rt393.e.push_back(e212);
				rt393.e.push_back(e3);
				rt393.calc_arity(nullptr);
				sprawformtree ft392 = std::make_shared<raw_form_tree>(elem::NONE, rt393);
				raw_term rt395;
				rt395.neg = false;
				rt395.extype = raw_term::REL;
				rt395.e.push_back(e153);
				rt395.e.push_back(e1);
				rt395.e.push_back(e196);
				rt395.e.push_back(e320);
				rt395.e.push_back(e218);
				rt395.e.push_back(e3);
				rt395.calc_arity(nullptr);
				sprawformtree ft394 = std::make_shared<raw_form_tree>(elem::NONE, rt395);
				sprawformtree ft391 = std::make_shared<raw_form_tree>(elem::AND, ft392, ft394);
				raw_term rt397;
				rt397.neg = false;
				rt397.extype = raw_term::REL;
				rt397.e.push_back(e303);
				rt397.e.push_back(e1);
				rt397.e.push_back(e210);
				rt397.e.push_back(e211);
				rt397.e.push_back(e195);
				rt397.e.push_back(e196);
				rt397.e.push_back(e59);
				rt397.e.push_back(e47);
				rt397.e.push_back(e3);
				rt397.calc_arity(nullptr);
				sprawformtree ft396 = std::make_shared<raw_form_tree>(elem::NONE, rt397);
				sprawformtree ft390 = std::make_shared<raw_form_tree>(elem::AND, ft391, ft396);
				raw_term rt400;
				rt400.neg = false;
				rt400.extype = raw_term::EQ;
				rt400.e.push_back(e368);
				rt400.e.push_back(e109);
				rt400.e.push_back(e59);
				rt400.calc_arity(nullptr);
				sprawformtree ft399 = std::make_shared<raw_form_tree>(elem::NONE, rt400);
				sprawformtree ft398 = std::make_shared<raw_form_tree>(elem::NOT, ft399);
				sprawformtree ft389 = std::make_shared<raw_form_tree>(elem::AND, ft390, ft398);
				sprawformtree ft403 = std::make_shared<raw_form_tree>(elem::VAR, e47);
				raw_term rt405;
				rt405.neg = false;
				rt405.extype = raw_term::REL;
				rt405.e.push_back(e308);
				rt405.e.push_back(e1);
				rt405.e.push_back(e210);
				rt405.e.push_back(e211);
				rt405.e.push_back(e59);
				rt405.e.push_back(e47);
				rt405.e.push_back(e3);
				rt405.calc_arity(nullptr);
				sprawformtree ft404 = std::make_shared<raw_form_tree>(elem::NONE, rt405);
				sprawformtree ft402 = std::make_shared<raw_form_tree>(elem::EXISTS, ft403, ft404);
				sprawformtree ft401 = std::make_shared<raw_form_tree>(elem::NOT, ft402);
				sprawformtree ft388 = std::make_shared<raw_form_tree>(elem::AND, ft389, ft401);
				raw_term rt408;
				rt408.neg = false;
				rt408.extype = raw_term::REL;
				rt408.e.push_back(e317);
				rt408.e.push_back(e1);
				rt408.e.push_back(e210);
				rt408.e.push_back(e211);
				rt408.e.push_back(e59);
				rt408.e.push_back(e3);
				rt408.calc_arity(nullptr);
				sprawformtree ft407 = std::make_shared<raw_form_tree>(elem::NONE, rt408);
				sprawformtree ft406 = std::make_shared<raw_form_tree>(elem::NOT, ft407);
				sprawformtree ft387 = std::make_shared<raw_form_tree>(elem::AND, ft388, ft406);
				raw_rule rr409;
				rr409.h.push_back(rt386);
				rr409.set_prft(ft387);
				raw_term rt410;
				rt410.neg = false;
				rt410.extype = raw_term::REL;
				rt410.e.push_back(e308);
				rt410.e.push_back(e1);
				rt410.e.push_back(e210);
				rt410.e.push_back(e211);
				rt410.e.push_back(e59);
				rt410.e.push_back(e47);
				rt410.e.push_back(e3);
				rt410.calc_arity(nullptr);
				raw_term rt416;
				rt416.neg = false;
				rt416.extype = raw_term::REL;
				rt416.e.push_back(e303);
				rt416.e.push_back(e1);
				rt416.e.push_back(e210);
				rt416.e.push_back(e211);
				rt416.e.push_back(e195);
				rt416.e.push_back(e196);
				rt416.e.push_back(e59);
				rt416.e.push_back(e47);
				rt416.e.push_back(e3);
				rt416.calc_arity(nullptr);
				sprawformtree ft415 = std::make_shared<raw_form_tree>(elem::NONE, rt416);
				raw_term rt418;
				rt418.neg = false;
				rt418.extype = raw_term::REL;
				rt418.e.push_back(e153);
				rt418.e.push_back(e1);
				rt418.e.push_back(e195);
				rt418.e.push_back(e3);
				rt418.calc_arity(nullptr);
				sprawformtree ft417 = std::make_shared<raw_form_tree>(elem::NONE, rt418);
				sprawformtree ft414 = std::make_shared<raw_form_tree>(elem::AND, ft415, ft417);
				raw_term rt420;
				rt420.neg = false;
				rt420.extype = raw_term::REL;
				rt420.e.push_back(e153);
				rt420.e.push_back(e1);
				rt420.e.push_back(e196);
				rt420.e.push_back(e3);
				rt420.calc_arity(nullptr);
				sprawformtree ft419 = std::make_shared<raw_form_tree>(elem::NONE, rt420);
				sprawformtree ft413 = std::make_shared<raw_form_tree>(elem::AND, ft414, ft419);
				sprawformtree ft423 = std::make_shared<raw_form_tree>(elem::VAR, e47);
				raw_term rt425;
				rt425.neg = false;
				rt425.extype = raw_term::REL;
				rt425.e.push_back(e308);
				rt425.e.push_back(e1);
				rt425.e.push_back(e210);
				rt425.e.push_back(e211);
				rt425.e.push_back(e59);
				rt425.e.push_back(e47);
				rt425.e.push_back(e3);
				rt425.calc_arity(nullptr);
				sprawformtree ft424 = std::make_shared<raw_form_tree>(elem::NONE, rt425);
				sprawformtree ft422 = std::make_shared<raw_form_tree>(elem::EXISTS, ft423, ft424);
				sprawformtree ft421 = std::make_shared<raw_form_tree>(elem::NOT, ft422);
				sprawformtree ft412 = std::make_shared<raw_form_tree>(elem::AND, ft413, ft421);
				raw_term rt428;
				rt428.neg = false;
				rt428.extype = raw_term::REL;
				rt428.e.push_back(e317);
				rt428.e.push_back(e1);
				rt428.e.push_back(e210);
				rt428.e.push_back(e211);
				rt428.e.push_back(e59);
				rt428.e.push_back(e3);
				rt428.calc_arity(nullptr);
				sprawformtree ft427 = std::make_shared<raw_form_tree>(elem::NONE, rt428);
				sprawformtree ft426 = std::make_shared<raw_form_tree>(elem::NOT, ft427);
				sprawformtree ft411 = std::make_shared<raw_form_tree>(elem::AND, ft412, ft426);
				raw_rule rr429;
				rr429.h.push_back(rt410);
				rr429.set_prft(ft411);
				raw_term rt430;
				rt430.neg = false;
				rt430.extype = raw_term::REL;
				rt430.e.push_back(e308);
				rt430.e.push_back(e1);
				rt430.e.push_back(e210);
				rt430.e.push_back(e211);
				rt430.e.push_back(e59);
				rt430.e.push_back(e47);
				rt430.e.push_back(e3);
				rt430.calc_arity(nullptr);
				raw_term rt437;
				rt437.neg = false;
				rt437.extype = raw_term::REL;
				rt437.e.push_back(e150);
				rt437.e.push_back(e1);
				rt437.e.push_back(e47);
				rt437.e.push_back(e3);
				rt437.calc_arity(nullptr);
				sprawformtree ft436 = std::make_shared<raw_form_tree>(elem::NONE, rt437);
				raw_term rt439;
				rt439.neg = false;
				rt439.extype = raw_term::REL;
				rt439.e.push_back(e303);
				rt439.e.push_back(e1);
				rt439.e.push_back(e210);
				rt439.e.push_back(e211);
				rt439.e.push_back(e195);
				rt439.e.push_back(e196);
				rt439.e.push_back(e59);
				rt439.e.push_back(e3);
				rt439.calc_arity(nullptr);
				sprawformtree ft438 = std::make_shared<raw_form_tree>(elem::NONE, rt439);
				sprawformtree ft435 = std::make_shared<raw_form_tree>(elem::AND, ft436, ft438);
				raw_term rt441;
				rt441.neg = false;
				rt441.extype = raw_term::REL;
				rt441.e.push_back(e153);
				rt441.e.push_back(e1);
				rt441.e.push_back(e195);
				rt441.e.push_back(e3);
				rt441.calc_arity(nullptr);
				sprawformtree ft440 = std::make_shared<raw_form_tree>(elem::NONE, rt441);
				sprawformtree ft434 = std::make_shared<raw_form_tree>(elem::AND, ft435, ft440);
				raw_term rt443;
				rt443.neg = false;
				rt443.extype = raw_term::REL;
				rt443.e.push_back(e153);
				rt443.e.push_back(e1);
				rt443.e.push_back(e196);
				rt443.e.push_back(e3);
				rt443.calc_arity(nullptr);
				sprawformtree ft442 = std::make_shared<raw_form_tree>(elem::NONE, rt443);
				sprawformtree ft433 = std::make_shared<raw_form_tree>(elem::AND, ft434, ft442);
				sprawformtree ft446 = std::make_shared<raw_form_tree>(elem::VAR, e47);
				raw_term rt448;
				rt448.neg = false;
				rt448.extype = raw_term::REL;
				rt448.e.push_back(e308);
				rt448.e.push_back(e1);
				rt448.e.push_back(e210);
				rt448.e.push_back(e211);
				rt448.e.push_back(e59);
				rt448.e.push_back(e47);
				rt448.e.push_back(e3);
				rt448.calc_arity(nullptr);
				sprawformtree ft447 = std::make_shared<raw_form_tree>(elem::NONE, rt448);
				sprawformtree ft445 = std::make_shared<raw_form_tree>(elem::EXISTS, ft446, ft447);
				sprawformtree ft444 = std::make_shared<raw_form_tree>(elem::NOT, ft445);
				sprawformtree ft432 = std::make_shared<raw_form_tree>(elem::AND, ft433, ft444);
				raw_term rt451;
				rt451.neg = false;
				rt451.extype = raw_term::REL;
				rt451.e.push_back(e317);
				rt451.e.push_back(e1);
				rt451.e.push_back(e210);
				rt451.e.push_back(e211);
				rt451.e.push_back(e59);
				rt451.e.push_back(e3);
				rt451.calc_arity(nullptr);
				sprawformtree ft450 = std::make_shared<raw_form_tree>(elem::NONE, rt451);
				sprawformtree ft449 = std::make_shared<raw_form_tree>(elem::NOT, ft450);
				sprawformtree ft431 = std::make_shared<raw_form_tree>(elem::AND, ft432, ft449);
				raw_rule rr452;
				rr452.h.push_back(rt430);
				rr452.set_prft(ft431);
				raw_term rt453;
				rt453.neg = true;
				rt453.extype = raw_term::REL;
				rt453.e.push_back(e303);
				rt453.e.push_back(e1);
				rt453.e.push_back(e210);
				rt453.e.push_back(e211);
				rt453.e.push_back(e195);
				rt453.e.push_back(e196);
				rt453.e.push_back(e59);
				rt453.e.push_back(e3);
				rt453.calc_arity(nullptr);
				raw_term rt454;
				rt454.neg = true;
				rt454.extype = raw_term::REL;
				rt454.e.push_back(e303);
				rt454.e.push_back(e1);
				rt454.e.push_back(e210);
				rt454.e.push_back(e211);
				rt454.e.push_back(e195);
				rt454.e.push_back(e196);
				rt454.e.push_back(e59);
				rt454.e.push_back(e47);
				rt454.e.push_back(e3);
				rt454.calc_arity(nullptr);
				raw_term rt457;
				rt457.neg = false;
				rt457.extype = raw_term::REL;
				rt457.e.push_back(e308);
				rt457.e.push_back(e1);
				rt457.e.push_back(e210);
				rt457.e.push_back(e211);
				rt457.e.push_back(e59);
				rt457.e.push_back(e162);
				rt457.e.push_back(e3);
				rt457.calc_arity(nullptr);
				sprawformtree ft456 = std::make_shared<raw_form_tree>(elem::NONE, rt457);
				raw_term rt459;
				rt459.neg = false;
				rt459.extype = raw_term::REL;
				rt459.e.push_back(e317);
				rt459.e.push_back(e1);
				rt459.e.push_back(e210);
				rt459.e.push_back(e211);
				rt459.e.push_back(e59);
				rt459.e.push_back(e3);
				rt459.calc_arity(nullptr);
				sprawformtree ft458 = std::make_shared<raw_form_tree>(elem::NONE, rt459);
				sprawformtree ft455 = std::make_shared<raw_form_tree>(elem::ALT, ft456, ft458);
				raw_rule rr460;
				rr460.h.push_back(rt453);
				rr460.h.push_back(rt454);
				rr460.set_prft(ft455);
				elem e461;
				e461.type = elem::SYM;
				e461.e = d.get_lexeme("ASSOC_LIST0");
				elem e462;
				e462.type = elem::VAR;
				e462.e = d.get_lexeme("?ts");
				elem e463;
				e463.type = elem::VAR;
				e463.e = d.get_lexeme("?us");
				raw_term rt464;
				rt464.neg = false;
				rt464.extype = raw_term::REL;
				rt464.e.push_back(e461);
				rt464.e.push_back(e1);
				rt464.e.push_back(e462);
				rt464.e.push_back(e195);
				rt464.e.push_back(e196);
				rt464.e.push_back(e462);
				rt464.e.push_back(e463);
				rt464.e.push_back(e3);
				rt464.calc_arity(nullptr);
				elem e468;
				e468.type = elem::SYM;
				e468.e = d.get_lexeme("ASSOC_LIST");
				raw_term rt469;
				rt469.neg = false;
				rt469.extype = raw_term::REL;
				rt469.e.push_back(e468);
				rt469.e.push_back(e1);
				rt469.e.push_back(e195);
				rt469.e.push_back(e196);
				rt469.e.push_back(e462);
				rt469.e.push_back(e3);
				rt469.calc_arity(nullptr);
				sprawformtree ft467 = std::make_shared<raw_form_tree>(elem::NONE, rt469);
				raw_term rt471;
				rt471.neg = false;
				rt471.extype = raw_term::REL;
				rt471.e.push_back(e153);
				rt471.e.push_back(e1);
				rt471.e.push_back(e463);
				rt471.e.push_back(e3);
				rt471.calc_arity(nullptr);
				sprawformtree ft470 = std::make_shared<raw_form_tree>(elem::NONE, rt471);
				sprawformtree ft466 = std::make_shared<raw_form_tree>(elem::AND, ft467, ft470);
				sprawformtree ft474 = std::make_shared<raw_form_tree>(elem::VAR, e162);
				raw_term rt476;
				rt476.neg = false;
				rt476.extype = raw_term::REL;
				rt476.e.push_back(e468);
				rt476.e.push_back(e1);
				rt476.e.push_back(e195);
				rt476.e.push_back(e196);
				rt476.e.push_back(e462);
				rt476.e.push_back(e162);
				rt476.e.push_back(e3);
				rt476.calc_arity(nullptr);
				sprawformtree ft475 = std::make_shared<raw_form_tree>(elem::NONE, rt476);
				sprawformtree ft473 = std::make_shared<raw_form_tree>(elem::EXISTS, ft474, ft475);
				sprawformtree ft472 = std::make_shared<raw_form_tree>(elem::NOT, ft473);
				sprawformtree ft465 = std::make_shared<raw_form_tree>(elem::AND, ft466, ft472);
				raw_rule rr477;
				rr477.h.push_back(rt464);
				rr477.set_prft(ft465);
				elem e478;
				e478.type = elem::VAR;
				e478.e = d.get_lexeme("?ts_hd");
				raw_term rt479;
				rt479.neg = false;
				rt479.extype = raw_term::REL;
				rt479.e.push_back(e308);
				rt479.e.push_back(e1);
				rt479.e.push_back(e195);
				rt479.e.push_back(e196);
				rt479.e.push_back(e478);
				rt479.e.push_back(e3);
				rt479.calc_arity(nullptr);
				elem e480;
				e480.type = elem::SYM;
				e480.e = d.get_lexeme("ASSOC_LIST1");
				elem e481;
				e481.type = elem::VAR;
				e481.e = d.get_lexeme("?ots");
				raw_term rt482;
				rt482.neg = false;
				rt482.extype = raw_term::REL;
				rt482.e.push_back(e480);
				rt482.e.push_back(e1);
				rt482.e.push_back(e481);
				rt482.e.push_back(e195);
				rt482.e.push_back(e196);
				rt482.e.push_back(e462);
				rt482.e.push_back(e463);
				rt482.e.push_back(e3);
				rt482.calc_arity(nullptr);
				raw_term rt486;
				rt486.neg = false;
				rt486.extype = raw_term::REL;
				rt486.e.push_back(e461);
				rt486.e.push_back(e1);
				rt486.e.push_back(e481);
				rt486.e.push_back(e195);
				rt486.e.push_back(e196);
				rt486.e.push_back(e462);
				rt486.e.push_back(e463);
				rt486.e.push_back(e3);
				rt486.calc_arity(nullptr);
				sprawformtree ft485 = std::make_shared<raw_form_tree>(elem::NONE, rt486);
				elem e488;
				e488.type = elem::VAR;
				e488.e = d.get_lexeme("?ts_tl");
				raw_term rt489;
				rt489.neg = false;
				rt489.extype = raw_term::REL;
				rt489.e.push_back(e153);
				rt489.e.push_back(e1);
				rt489.e.push_back(e462);
				rt489.e.push_back(e478);
				rt489.e.push_back(e488);
				rt489.e.push_back(e3);
				rt489.calc_arity(nullptr);
				sprawformtree ft487 = std::make_shared<raw_form_tree>(elem::NONE, rt489);
				sprawformtree ft484 = std::make_shared<raw_form_tree>(elem::AND, ft485, ft487);
				sprawformtree ft492 = std::make_shared<raw_form_tree>(elem::VAR, e162);
				raw_term rt494;
				rt494.neg = false;
				rt494.extype = raw_term::REL;
				rt494.e.push_back(e468);
				rt494.e.push_back(e1);
				rt494.e.push_back(e195);
				rt494.e.push_back(e196);
				rt494.e.push_back(e481);
				rt494.e.push_back(e162);
				rt494.e.push_back(e3);
				rt494.calc_arity(nullptr);
				sprawformtree ft493 = std::make_shared<raw_form_tree>(elem::NONE, rt494);
				sprawformtree ft491 = std::make_shared<raw_form_tree>(elem::EXISTS, ft492, ft493);
				sprawformtree ft490 = std::make_shared<raw_form_tree>(elem::NOT, ft491);
				sprawformtree ft483 = std::make_shared<raw_form_tree>(elem::AND, ft484, ft490);
				raw_rule rr495;
				rr495.h.push_back(rt479);
				rr495.h.push_back(rt482);
				rr495.set_prft(ft483);
				elem e496;
				e496.type = elem::VAR;
				e496.e = d.get_lexeme("?nus");
				raw_term rt497;
				rt497.neg = false;
				rt497.extype = raw_term::REL;
				rt497.e.push_back(e461);
				rt497.e.push_back(e1);
				rt497.e.push_back(e481);
				rt497.e.push_back(e195);
				rt497.e.push_back(e196);
				rt497.e.push_back(e488);
				rt497.e.push_back(e496);
				rt497.e.push_back(e3);
				rt497.calc_arity(nullptr);
				raw_term rt503;
				rt503.neg = false;
				rt503.extype = raw_term::REL;
				rt503.e.push_back(e480);
				rt503.e.push_back(e1);
				rt503.e.push_back(e481);
				rt503.e.push_back(e195);
				rt503.e.push_back(e196);
				rt503.e.push_back(e462);
				rt503.e.push_back(e463);
				rt503.e.push_back(e3);
				rt503.calc_arity(nullptr);
				sprawformtree ft502 = std::make_shared<raw_form_tree>(elem::NONE, rt503);
				raw_term rt505;
				rt505.neg = false;
				rt505.extype = raw_term::REL;
				rt505.e.push_back(e153);
				rt505.e.push_back(e1);
				rt505.e.push_back(e462);
				rt505.e.push_back(e478);
				rt505.e.push_back(e488);
				rt505.e.push_back(e3);
				rt505.calc_arity(nullptr);
				sprawformtree ft504 = std::make_shared<raw_form_tree>(elem::NONE, rt505);
				sprawformtree ft501 = std::make_shared<raw_form_tree>(elem::AND, ft502, ft504);
				elem e507;
				e507.type = elem::VAR;
				e507.e = d.get_lexeme("?nus_hd");
				raw_term rt508;
				rt508.neg = false;
				rt508.extype = raw_term::REL;
				rt508.e.push_back(e308);
				rt508.e.push_back(e1);
				rt508.e.push_back(e195);
				rt508.e.push_back(e196);
				rt508.e.push_back(e478);
				rt508.e.push_back(e507);
				rt508.e.push_back(e3);
				rt508.calc_arity(nullptr);
				sprawformtree ft506 = std::make_shared<raw_form_tree>(elem::NONE, rt508);
				sprawformtree ft500 = std::make_shared<raw_form_tree>(elem::AND, ft501, ft506);
				raw_term rt510;
				rt510.neg = false;
				rt510.extype = raw_term::REL;
				rt510.e.push_back(e153);
				rt510.e.push_back(e1);
				rt510.e.push_back(e496);
				rt510.e.push_back(e507);
				rt510.e.push_back(e463);
				rt510.e.push_back(e3);
				rt510.calc_arity(nullptr);
				sprawformtree ft509 = std::make_shared<raw_form_tree>(elem::NONE, rt510);
				sprawformtree ft499 = std::make_shared<raw_form_tree>(elem::AND, ft500, ft509);
				sprawformtree ft513 = std::make_shared<raw_form_tree>(elem::VAR, e162);
				raw_term rt515;
				rt515.neg = false;
				rt515.extype = raw_term::REL;
				rt515.e.push_back(e468);
				rt515.e.push_back(e1);
				rt515.e.push_back(e195);
				rt515.e.push_back(e196);
				rt515.e.push_back(e481);
				rt515.e.push_back(e162);
				rt515.e.push_back(e3);
				rt515.calc_arity(nullptr);
				sprawformtree ft514 = std::make_shared<raw_form_tree>(elem::NONE, rt515);
				sprawformtree ft512 = std::make_shared<raw_form_tree>(elem::EXISTS, ft513, ft514);
				sprawformtree ft511 = std::make_shared<raw_form_tree>(elem::NOT, ft512);
				sprawformtree ft498 = std::make_shared<raw_form_tree>(elem::AND, ft499, ft511);
				raw_rule rr516;
				rr516.h.push_back(rt497);
				rr516.set_prft(ft498);
				raw_term rt517;
				rt517.neg = false;
				rt517.extype = raw_term::REL;
				rt517.e.push_back(e250);
				rt517.e.push_back(e1);
				rt517.e.push_back(e463);
				rt517.e.push_back(e3);
				rt517.calc_arity(nullptr);
				elem e518;
				e518.type = elem::SYM;
				e518.e = d.get_lexeme("ASSOC_LIST2");
				raw_term rt519;
				rt519.neg = false;
				rt519.extype = raw_term::REL;
				rt519.e.push_back(e518);
				rt519.e.push_back(e1);
				rt519.e.push_back(e481);
				rt519.e.push_back(e195);
				rt519.e.push_back(e196);
				rt519.e.push_back(e462);
				rt519.e.push_back(e463);
				rt519.e.push_back(e3);
				rt519.calc_arity(nullptr);
				raw_term rt523;
				rt523.neg = false;
				rt523.extype = raw_term::REL;
				rt523.e.push_back(e461);
				rt523.e.push_back(e1);
				rt523.e.push_back(e481);
				rt523.e.push_back(e195);
				rt523.e.push_back(e196);
				rt523.e.push_back(e462);
				rt523.e.push_back(e463);
				rt523.e.push_back(e3);
				rt523.calc_arity(nullptr);
				sprawformtree ft522 = std::make_shared<raw_form_tree>(elem::NONE, rt523);
				raw_term rt525;
				rt525.neg = false;
				rt525.extype = raw_term::REL;
				rt525.e.push_back(e153);
				rt525.e.push_back(e1);
				rt525.e.push_back(e462);
				rt525.e.push_back(e3);
				rt525.calc_arity(nullptr);
				sprawformtree ft524 = std::make_shared<raw_form_tree>(elem::NONE, rt525);
				sprawformtree ft521 = std::make_shared<raw_form_tree>(elem::AND, ft522, ft524);
				sprawformtree ft528 = std::make_shared<raw_form_tree>(elem::VAR, e162);
				raw_term rt530;
				rt530.neg = false;
				rt530.extype = raw_term::REL;
				rt530.e.push_back(e468);
				rt530.e.push_back(e1);
				rt530.e.push_back(e195);
				rt530.e.push_back(e196);
				rt530.e.push_back(e481);
				rt530.e.push_back(e162);
				rt530.e.push_back(e3);
				rt530.calc_arity(nullptr);
				sprawformtree ft529 = std::make_shared<raw_form_tree>(elem::NONE, rt530);
				sprawformtree ft527 = std::make_shared<raw_form_tree>(elem::EXISTS, ft528, ft529);
				sprawformtree ft526 = std::make_shared<raw_form_tree>(elem::NOT, ft527);
				sprawformtree ft520 = std::make_shared<raw_form_tree>(elem::AND, ft521, ft526);
				raw_rule rr531;
				rr531.h.push_back(rt517);
				rr531.h.push_back(rt519);
				rr531.set_prft(ft520);
				raw_term rt532;
				rt532.neg = false;
				rt532.extype = raw_term::REL;
				rt532.e.push_back(e468);
				rt532.e.push_back(e1);
				rt532.e.push_back(e195);
				rt532.e.push_back(e196);
				rt532.e.push_back(e481);
				rt532.e.push_back(e496);
				rt532.e.push_back(e3);
				rt532.calc_arity(nullptr);
				raw_term rt537;
				rt537.neg = false;
				rt537.extype = raw_term::REL;
				rt537.e.push_back(e518);
				rt537.e.push_back(e1);
				rt537.e.push_back(e481);
				rt537.e.push_back(e195);
				rt537.e.push_back(e196);
				rt537.e.push_back(e462);
				rt537.e.push_back(e463);
				rt537.e.push_back(e3);
				rt537.calc_arity(nullptr);
				sprawformtree ft536 = std::make_shared<raw_form_tree>(elem::NONE, rt537);
				raw_term rt539;
				rt539.neg = false;
				rt539.extype = raw_term::REL;
				rt539.e.push_back(e263);
				rt539.e.push_back(e1);
				rt539.e.push_back(e463);
				rt539.e.push_back(e496);
				rt539.e.push_back(e3);
				rt539.calc_arity(nullptr);
				sprawformtree ft538 = std::make_shared<raw_form_tree>(elem::NONE, rt539);
				sprawformtree ft535 = std::make_shared<raw_form_tree>(elem::AND, ft536, ft538);
				raw_term rt541;
				rt541.neg = false;
				rt541.extype = raw_term::REL;
				rt541.e.push_back(e153);
				rt541.e.push_back(e1);
				rt541.e.push_back(e462);
				rt541.e.push_back(e3);
				rt541.calc_arity(nullptr);
				sprawformtree ft540 = std::make_shared<raw_form_tree>(elem::NONE, rt541);
				sprawformtree ft534 = std::make_shared<raw_form_tree>(elem::AND, ft535, ft540);
				sprawformtree ft544 = std::make_shared<raw_form_tree>(elem::VAR, e162);
				raw_term rt546;
				rt546.neg = false;
				rt546.extype = raw_term::REL;
				rt546.e.push_back(e468);
				rt546.e.push_back(e1);
				rt546.e.push_back(e195);
				rt546.e.push_back(e196);
				rt546.e.push_back(e481);
				rt546.e.push_back(e162);
				rt546.e.push_back(e3);
				rt546.calc_arity(nullptr);
				sprawformtree ft545 = std::make_shared<raw_form_tree>(elem::NONE, rt546);
				sprawformtree ft543 = std::make_shared<raw_form_tree>(elem::EXISTS, ft544, ft545);
				sprawformtree ft542 = std::make_shared<raw_form_tree>(elem::NOT, ft543);
				sprawformtree ft533 = std::make_shared<raw_form_tree>(elem::AND, ft534, ft542);
				raw_rule rr547;
				rr547.h.push_back(rt532);
				rr547.set_prft(ft533);
				raw_term rt548;
				rt548.neg = true;
				rt548.extype = raw_term::REL;
				rt548.e.push_back(e461);
				rt548.e.push_back(e1);
				rt548.e.push_back(e481);
				rt548.e.push_back(e195);
				rt548.e.push_back(e196);
				rt548.e.push_back(e488);
				rt548.e.push_back(e496);
				rt548.e.push_back(e3);
				rt548.calc_arity(nullptr);
				raw_term rt549;
				rt549.neg = true;
				rt549.extype = raw_term::REL;
				rt549.e.push_back(e480);
				rt549.e.push_back(e1);
				rt549.e.push_back(e481);
				rt549.e.push_back(e195);
				rt549.e.push_back(e196);
				rt549.e.push_back(e462);
				rt549.e.push_back(e463);
				rt549.e.push_back(e3);
				rt549.calc_arity(nullptr);
				raw_term rt550;
				rt550.neg = true;
				rt550.extype = raw_term::REL;
				rt550.e.push_back(e518);
				rt550.e.push_back(e1);
				rt550.e.push_back(e481);
				rt550.e.push_back(e195);
				rt550.e.push_back(e196);
				rt550.e.push_back(e462);
				rt550.e.push_back(e463);
				rt550.e.push_back(e3);
				rt550.calc_arity(nullptr);
				raw_term rt552;
				rt552.neg = false;
				rt552.extype = raw_term::REL;
				rt552.e.push_back(e468);
				rt552.e.push_back(e1);
				rt552.e.push_back(e195);
				rt552.e.push_back(e196);
				rt552.e.push_back(e481);
				rt552.e.push_back(e162);
				rt552.e.push_back(e3);
				rt552.calc_arity(nullptr);
				sprawformtree ft551 = std::make_shared<raw_form_tree>(elem::NONE, rt552);
				raw_rule rr553;
				rr553.h.push_back(rt548);
				rr553.h.push_back(rt549);
				rr553.h.push_back(rt550);
				rr553.set_prft(ft551);
				elem e554;
				e554.type = elem::SYM;
				e554.e = d.get_lexeme("IS_CONSISTENT0");
				raw_term rt555;
				rt555.neg = false;
				rt555.extype = raw_term::REL;
				rt555.e.push_back(e554);
				rt555.e.push_back(e1);
				rt555.e.push_back(e195);
				rt555.e.push_back(e196);
				rt555.e.push_back(e195);
				rt555.e.push_back(e196);
				rt555.e.push_back(e59);
				rt555.e.push_back(e47);
				rt555.e.push_back(e3);
				rt555.calc_arity(nullptr);
				elem e559;
				e559.type = elem::SYM;
				e559.e = d.get_lexeme("IS_ASSOC_CONSISTENT");
				raw_term rt560;
				rt560.neg = false;
				rt560.extype = raw_term::REL;
				rt560.e.push_back(e559);
				rt560.e.push_back(e1);
				rt560.e.push_back(e195);
				rt560.e.push_back(e196);
				rt560.e.push_back(e59);
				rt560.e.push_back(e47);
				rt560.e.push_back(e3);
				rt560.calc_arity(nullptr);
				sprawformtree ft558 = std::make_shared<raw_form_tree>(elem::NONE, rt560);
				elem e563;
				e563.type = elem::SYM;
				e563.e = d.get_lexeme("CONSISTENT");
				raw_term rt564;
				rt564.neg = false;
				rt564.extype = raw_term::REL;
				rt564.e.push_back(e563);
				rt564.e.push_back(e1);
				rt564.e.push_back(e195);
				rt564.e.push_back(e196);
				rt564.e.push_back(e59);
				rt564.e.push_back(e47);
				rt564.e.push_back(e3);
				rt564.calc_arity(nullptr);
				sprawformtree ft562 = std::make_shared<raw_form_tree>(elem::NONE, rt564);
				sprawformtree ft561 = std::make_shared<raw_form_tree>(elem::NOT, ft562);
				sprawformtree ft557 = std::make_shared<raw_form_tree>(elem::AND, ft558, ft561);
				elem e567;
				e567.type = elem::SYM;
				e567.e = d.get_lexeme("NOT_CONSISTENT");
				raw_term rt568;
				rt568.neg = false;
				rt568.extype = raw_term::REL;
				rt568.e.push_back(e567);
				rt568.e.push_back(e1);
				rt568.e.push_back(e195);
				rt568.e.push_back(e196);
				rt568.e.push_back(e59);
				rt568.e.push_back(e47);
				rt568.e.push_back(e3);
				rt568.calc_arity(nullptr);
				sprawformtree ft566 = std::make_shared<raw_form_tree>(elem::NONE, rt568);
				sprawformtree ft565 = std::make_shared<raw_form_tree>(elem::NOT, ft566);
				sprawformtree ft556 = std::make_shared<raw_form_tree>(elem::AND, ft557, ft565);
				raw_rule rr569;
				rr569.h.push_back(rt555);
				rr569.set_prft(ft556);
				raw_term rt570;
				rt570.neg = false;
				rt570.extype = raw_term::REL;
				rt570.e.push_back(e554);
				rt570.e.push_back(e1);
				rt570.e.push_back(e210);
				rt570.e.push_back(e211);
				rt570.e.push_back(e212);
				rt570.e.push_back(e218);
				rt570.e.push_back(e59);
				rt570.e.push_back(e47);
				rt570.e.push_back(e3);
				rt570.calc_arity(nullptr);
				raw_term rt576;
				rt576.neg = false;
				rt576.extype = raw_term::REL;
				rt576.e.push_back(e153);
				rt576.e.push_back(e1);
				rt576.e.push_back(e195);
				rt576.e.push_back(e59);
				rt576.e.push_back(e212);
				rt576.e.push_back(e3);
				rt576.calc_arity(nullptr);
				sprawformtree ft575 = std::make_shared<raw_form_tree>(elem::NONE, rt576);
				raw_term rt578;
				rt578.neg = false;
				rt578.extype = raw_term::REL;
				rt578.e.push_back(e153);
				rt578.e.push_back(e1);
				rt578.e.push_back(e196);
				rt578.e.push_back(e47);
				rt578.e.push_back(e218);
				rt578.e.push_back(e3);
				rt578.calc_arity(nullptr);
				sprawformtree ft577 = std::make_shared<raw_form_tree>(elem::NONE, rt578);
				sprawformtree ft574 = std::make_shared<raw_form_tree>(elem::AND, ft575, ft577);
				raw_term rt580;
				rt580.neg = false;
				rt580.extype = raw_term::REL;
				rt580.e.push_back(e554);
				rt580.e.push_back(e1);
				rt580.e.push_back(e210);
				rt580.e.push_back(e211);
				rt580.e.push_back(e195);
				rt580.e.push_back(e196);
				rt580.e.push_back(e59);
				rt580.e.push_back(e47);
				rt580.e.push_back(e3);
				rt580.calc_arity(nullptr);
				sprawformtree ft579 = std::make_shared<raw_form_tree>(elem::NONE, rt580);
				sprawformtree ft573 = std::make_shared<raw_form_tree>(elem::AND, ft574, ft579);
				raw_term rt583;
				rt583.neg = false;
				rt583.extype = raw_term::REL;
				rt583.e.push_back(e563);
				rt583.e.push_back(e1);
				rt583.e.push_back(e210);
				rt583.e.push_back(e211);
				rt583.e.push_back(e59);
				rt583.e.push_back(e47);
				rt583.e.push_back(e3);
				rt583.calc_arity(nullptr);
				sprawformtree ft582 = std::make_shared<raw_form_tree>(elem::NONE, rt583);
				sprawformtree ft581 = std::make_shared<raw_form_tree>(elem::NOT, ft582);
				sprawformtree ft572 = std::make_shared<raw_form_tree>(elem::AND, ft573, ft581);
				raw_term rt586;
				rt586.neg = false;
				rt586.extype = raw_term::REL;
				rt586.e.push_back(e567);
				rt586.e.push_back(e1);
				rt586.e.push_back(e210);
				rt586.e.push_back(e211);
				rt586.e.push_back(e59);
				rt586.e.push_back(e47);
				rt586.e.push_back(e3);
				rt586.calc_arity(nullptr);
				sprawformtree ft585 = std::make_shared<raw_form_tree>(elem::NONE, rt586);
				sprawformtree ft584 = std::make_shared<raw_form_tree>(elem::NOT, ft585);
				sprawformtree ft571 = std::make_shared<raw_form_tree>(elem::AND, ft572, ft584);
				raw_rule rr587;
				rr587.h.push_back(rt570);
				rr587.set_prft(ft571);
				raw_term rt588;
				rt588.neg = false;
				rt588.extype = raw_term::REL;
				rt588.e.push_back(e554);
				rt588.e.push_back(e1);
				rt588.e.push_back(e210);
				rt588.e.push_back(e211);
				rt588.e.push_back(e212);
				rt588.e.push_back(e218);
				rt588.e.push_back(e59);
				rt588.e.push_back(e47);
				rt588.e.push_back(e3);
				rt588.calc_arity(nullptr);
				raw_term rt596;
				rt596.neg = false;
				rt596.extype = raw_term::REL;
				rt596.e.push_back(e153);
				rt596.e.push_back(e1);
				rt596.e.push_back(e195);
				rt596.e.push_back(e59);
				rt596.e.push_back(e212);
				rt596.e.push_back(e3);
				rt596.calc_arity(nullptr);
				sprawformtree ft595 = std::make_shared<raw_form_tree>(elem::NONE, rt596);
				sprawformtree ft594 = std::make_shared<raw_form_tree>(elem::NOT, ft595);
				raw_term rt598;
				rt598.neg = false;
				rt598.extype = raw_term::REL;
				rt598.e.push_back(e153);
				rt598.e.push_back(e1);
				rt598.e.push_back(e195);
				rt598.e.push_back(e221);
				rt598.e.push_back(e212);
				rt598.e.push_back(e3);
				rt598.calc_arity(nullptr);
				sprawformtree ft597 = std::make_shared<raw_form_tree>(elem::NONE, rt598);
				sprawformtree ft593 = std::make_shared<raw_form_tree>(elem::AND, ft594, ft597);
				elem e600;
				e600.type = elem::VAR;
				e600.e = d.get_lexeme("?ys_hd");
				raw_term rt601;
				rt601.neg = false;
				rt601.extype = raw_term::REL;
				rt601.e.push_back(e153);
				rt601.e.push_back(e1);
				rt601.e.push_back(e196);
				rt601.e.push_back(e600);
				rt601.e.push_back(e218);
				rt601.e.push_back(e3);
				rt601.calc_arity(nullptr);
				sprawformtree ft599 = std::make_shared<raw_form_tree>(elem::NONE, rt601);
				sprawformtree ft592 = std::make_shared<raw_form_tree>(elem::AND, ft593, ft599);
				raw_term rt603;
				rt603.neg = false;
				rt603.extype = raw_term::REL;
				rt603.e.push_back(e554);
				rt603.e.push_back(e1);
				rt603.e.push_back(e210);
				rt603.e.push_back(e211);
				rt603.e.push_back(e195);
				rt603.e.push_back(e196);
				rt603.e.push_back(e59);
				rt603.e.push_back(e47);
				rt603.e.push_back(e3);
				rt603.calc_arity(nullptr);
				sprawformtree ft602 = std::make_shared<raw_form_tree>(elem::NONE, rt603);
				sprawformtree ft591 = std::make_shared<raw_form_tree>(elem::AND, ft592, ft602);
				raw_term rt606;
				rt606.neg = false;
				rt606.extype = raw_term::REL;
				rt606.e.push_back(e563);
				rt606.e.push_back(e1);
				rt606.e.push_back(e210);
				rt606.e.push_back(e211);
				rt606.e.push_back(e59);
				rt606.e.push_back(e47);
				rt606.e.push_back(e3);
				rt606.calc_arity(nullptr);
				sprawformtree ft605 = std::make_shared<raw_form_tree>(elem::NONE, rt606);
				sprawformtree ft604 = std::make_shared<raw_form_tree>(elem::NOT, ft605);
				sprawformtree ft590 = std::make_shared<raw_form_tree>(elem::AND, ft591, ft604);
				raw_term rt609;
				rt609.neg = false;
				rt609.extype = raw_term::REL;
				rt609.e.push_back(e567);
				rt609.e.push_back(e1);
				rt609.e.push_back(e210);
				rt609.e.push_back(e211);
				rt609.e.push_back(e59);
				rt609.e.push_back(e47);
				rt609.e.push_back(e3);
				rt609.calc_arity(nullptr);
				sprawformtree ft608 = std::make_shared<raw_form_tree>(elem::NONE, rt609);
				sprawformtree ft607 = std::make_shared<raw_form_tree>(elem::NOT, ft608);
				sprawformtree ft589 = std::make_shared<raw_form_tree>(elem::AND, ft590, ft607);
				raw_rule rr610;
				rr610.h.push_back(rt588);
				rr610.set_prft(ft589);
				raw_term rt611;
				rt611.neg = false;
				rt611.extype = raw_term::REL;
				rt611.e.push_back(e567);
				rt611.e.push_back(e1);
				rt611.e.push_back(e210);
				rt611.e.push_back(e211);
				rt611.e.push_back(e59);
				rt611.e.push_back(e47);
				rt611.e.push_back(e3);
				rt611.calc_arity(nullptr);
				raw_term rt618;
				rt618.neg = false;
				rt618.extype = raw_term::REL;
				rt618.e.push_back(e153);
				rt618.e.push_back(e1);
				rt618.e.push_back(e195);
				rt618.e.push_back(e59);
				rt618.e.push_back(e212);
				rt618.e.push_back(e3);
				rt618.calc_arity(nullptr);
				sprawformtree ft617 = std::make_shared<raw_form_tree>(elem::NONE, rt618);
				raw_term rt621;
				rt621.neg = false;
				rt621.extype = raw_term::REL;
				rt621.e.push_back(e153);
				rt621.e.push_back(e1);
				rt621.e.push_back(e196);
				rt621.e.push_back(e47);
				rt621.e.push_back(e218);
				rt621.e.push_back(e3);
				rt621.calc_arity(nullptr);
				sprawformtree ft620 = std::make_shared<raw_form_tree>(elem::NONE, rt621);
				sprawformtree ft619 = std::make_shared<raw_form_tree>(elem::NOT, ft620);
				sprawformtree ft616 = std::make_shared<raw_form_tree>(elem::AND, ft617, ft619);
				elem e623;
				e623.type = elem::VAR;
				e623.e = d.get_lexeme("?ay");
				raw_term rt624;
				rt624.neg = false;
				rt624.extype = raw_term::REL;
				rt624.e.push_back(e153);
				rt624.e.push_back(e1);
				rt624.e.push_back(e196);
				rt624.e.push_back(e623);
				rt624.e.push_back(e218);
				rt624.e.push_back(e3);
				rt624.calc_arity(nullptr);
				sprawformtree ft622 = std::make_shared<raw_form_tree>(elem::NONE, rt624);
				sprawformtree ft615 = std::make_shared<raw_form_tree>(elem::AND, ft616, ft622);
				raw_term rt626;
				rt626.neg = false;
				rt626.extype = raw_term::REL;
				rt626.e.push_back(e554);
				rt626.e.push_back(e1);
				rt626.e.push_back(e210);
				rt626.e.push_back(e211);
				rt626.e.push_back(e195);
				rt626.e.push_back(e196);
				rt626.e.push_back(e59);
				rt626.e.push_back(e47);
				rt626.e.push_back(e3);
				rt626.calc_arity(nullptr);
				sprawformtree ft625 = std::make_shared<raw_form_tree>(elem::NONE, rt626);
				sprawformtree ft614 = std::make_shared<raw_form_tree>(elem::AND, ft615, ft625);
				raw_term rt629;
				rt629.neg = false;
				rt629.extype = raw_term::REL;
				rt629.e.push_back(e563);
				rt629.e.push_back(e1);
				rt629.e.push_back(e210);
				rt629.e.push_back(e211);
				rt629.e.push_back(e59);
				rt629.e.push_back(e47);
				rt629.e.push_back(e3);
				rt629.calc_arity(nullptr);
				sprawformtree ft628 = std::make_shared<raw_form_tree>(elem::NONE, rt629);
				sprawformtree ft627 = std::make_shared<raw_form_tree>(elem::NOT, ft628);
				sprawformtree ft613 = std::make_shared<raw_form_tree>(elem::AND, ft614, ft627);
				raw_term rt632;
				rt632.neg = false;
				rt632.extype = raw_term::REL;
				rt632.e.push_back(e567);
				rt632.e.push_back(e1);
				rt632.e.push_back(e210);
				rt632.e.push_back(e211);
				rt632.e.push_back(e59);
				rt632.e.push_back(e47);
				rt632.e.push_back(e3);
				rt632.calc_arity(nullptr);
				sprawformtree ft631 = std::make_shared<raw_form_tree>(elem::NONE, rt632);
				sprawformtree ft630 = std::make_shared<raw_form_tree>(elem::NOT, ft631);
				sprawformtree ft612 = std::make_shared<raw_form_tree>(elem::AND, ft613, ft630);
				raw_rule rr633;
				rr633.h.push_back(rt611);
				rr633.set_prft(ft612);
				raw_term rt634;
				rt634.neg = false;
				rt634.extype = raw_term::REL;
				rt634.e.push_back(e563);
				rt634.e.push_back(e1);
				rt634.e.push_back(e210);
				rt634.e.push_back(e211);
				rt634.e.push_back(e59);
				rt634.e.push_back(e47);
				rt634.e.push_back(e3);
				rt634.calc_arity(nullptr);
				raw_term rt640;
				rt640.neg = false;
				rt640.extype = raw_term::REL;
				rt640.e.push_back(e554);
				rt640.e.push_back(e1);
				rt640.e.push_back(e210);
				rt640.e.push_back(e211);
				rt640.e.push_back(e195);
				rt640.e.push_back(e196);
				rt640.e.push_back(e59);
				rt640.e.push_back(e47);
				rt640.e.push_back(e3);
				rt640.calc_arity(nullptr);
				sprawformtree ft639 = std::make_shared<raw_form_tree>(elem::NONE, rt640);
				raw_term rt642;
				rt642.neg = false;
				rt642.extype = raw_term::REL;
				rt642.e.push_back(e153);
				rt642.e.push_back(e1);
				rt642.e.push_back(e195);
				rt642.e.push_back(e3);
				rt642.calc_arity(nullptr);
				sprawformtree ft641 = std::make_shared<raw_form_tree>(elem::NONE, rt642);
				sprawformtree ft638 = std::make_shared<raw_form_tree>(elem::AND, ft639, ft641);
				raw_term rt644;
				rt644.neg = false;
				rt644.extype = raw_term::REL;
				rt644.e.push_back(e153);
				rt644.e.push_back(e1);
				rt644.e.push_back(e196);
				rt644.e.push_back(e3);
				rt644.calc_arity(nullptr);
				sprawformtree ft643 = std::make_shared<raw_form_tree>(elem::NONE, rt644);
				sprawformtree ft637 = std::make_shared<raw_form_tree>(elem::AND, ft638, ft643);
				raw_term rt647;
				rt647.neg = false;
				rt647.extype = raw_term::REL;
				rt647.e.push_back(e563);
				rt647.e.push_back(e1);
				rt647.e.push_back(e210);
				rt647.e.push_back(e211);
				rt647.e.push_back(e59);
				rt647.e.push_back(e47);
				rt647.e.push_back(e3);
				rt647.calc_arity(nullptr);
				sprawformtree ft646 = std::make_shared<raw_form_tree>(elem::NONE, rt647);
				sprawformtree ft645 = std::make_shared<raw_form_tree>(elem::NOT, ft646);
				sprawformtree ft636 = std::make_shared<raw_form_tree>(elem::AND, ft637, ft645);
				raw_term rt650;
				rt650.neg = false;
				rt650.extype = raw_term::REL;
				rt650.e.push_back(e567);
				rt650.e.push_back(e1);
				rt650.e.push_back(e210);
				rt650.e.push_back(e211);
				rt650.e.push_back(e59);
				rt650.e.push_back(e47);
				rt650.e.push_back(e3);
				rt650.calc_arity(nullptr);
				sprawformtree ft649 = std::make_shared<raw_form_tree>(elem::NONE, rt650);
				sprawformtree ft648 = std::make_shared<raw_form_tree>(elem::NOT, ft649);
				sprawformtree ft635 = std::make_shared<raw_form_tree>(elem::AND, ft636, ft648);
				raw_rule rr651;
				rr651.h.push_back(rt634);
				rr651.set_prft(ft635);
				raw_term rt652;
				rt652.neg = true;
				rt652.extype = raw_term::REL;
				rt652.e.push_back(e554);
				rt652.e.push_back(e1);
				rt652.e.push_back(e210);
				rt652.e.push_back(e211);
				rt652.e.push_back(e212);
				rt652.e.push_back(e218);
				rt652.e.push_back(e59);
				rt652.e.push_back(e47);
				rt652.e.push_back(e3);
				rt652.calc_arity(nullptr);
				raw_term rt655;
				rt655.neg = false;
				rt655.extype = raw_term::REL;
				rt655.e.push_back(e563);
				rt655.e.push_back(e1);
				rt655.e.push_back(e210);
				rt655.e.push_back(e211);
				rt655.e.push_back(e59);
				rt655.e.push_back(e47);
				rt655.e.push_back(e3);
				rt655.calc_arity(nullptr);
				sprawformtree ft654 = std::make_shared<raw_form_tree>(elem::NONE, rt655);
				raw_term rt657;
				rt657.neg = false;
				rt657.extype = raw_term::REL;
				rt657.e.push_back(e567);
				rt657.e.push_back(e1);
				rt657.e.push_back(e210);
				rt657.e.push_back(e211);
				rt657.e.push_back(e59);
				rt657.e.push_back(e47);
				rt657.e.push_back(e3);
				rt657.calc_arity(nullptr);
				sprawformtree ft656 = std::make_shared<raw_form_tree>(elem::NONE, rt657);
				sprawformtree ft653 = std::make_shared<raw_form_tree>(elem::ALT, ft654, ft656);
				raw_rule rr658;
				rr658.h.push_back(rt652);
				rr658.set_prft(ft653);
				elem e659;
				e659.type = elem::SYM;
				e659.e = d.get_lexeme("IS_DICT_CONSISTENT0");
				raw_term rt660;
				rt660.neg = false;
				rt660.extype = raw_term::REL;
				rt660.e.push_back(e659);
				rt660.e.push_back(e1);
				rt660.e.push_back(e195);
				rt660.e.push_back(e196);
				rt660.e.push_back(e195);
				rt660.e.push_back(e196);
				rt660.e.push_back(e3);
				rt660.calc_arity(nullptr);
				elem e664;
				e664.type = elem::SYM;
				e664.e = d.get_lexeme("IS_DICT_CONSISTENT");
				raw_term rt665;
				rt665.neg = false;
				rt665.extype = raw_term::REL;
				rt665.e.push_back(e664);
				rt665.e.push_back(e1);
				rt665.e.push_back(e195);
				rt665.e.push_back(e196);
				rt665.e.push_back(e3);
				rt665.calc_arity(nullptr);
				sprawformtree ft663 = std::make_shared<raw_form_tree>(elem::NONE, rt665);
				elem e668;
				e668.type = elem::SYM;
				e668.e = d.get_lexeme("DICT_CONSISTENT");
				raw_term rt669;
				rt669.neg = false;
				rt669.extype = raw_term::REL;
				rt669.e.push_back(e668);
				rt669.e.push_back(e1);
				rt669.e.push_back(e195);
				rt669.e.push_back(e196);
				rt669.e.push_back(e3);
				rt669.calc_arity(nullptr);
				sprawformtree ft667 = std::make_shared<raw_form_tree>(elem::NONE, rt669);
				sprawformtree ft666 = std::make_shared<raw_form_tree>(elem::NOT, ft667);
				sprawformtree ft662 = std::make_shared<raw_form_tree>(elem::AND, ft663, ft666);
				sprawformtree ft672 = std::make_shared<raw_form_tree>(elem::VAR, e162);
				sprawformtree ft674 = std::make_shared<raw_form_tree>(elem::VAR, e39);
				elem e676;
				e676.type = elem::SYM;
				e676.e = d.get_lexeme("NOT_DICT_CONSISTENT");
				raw_term rt677;
				rt677.neg = false;
				rt677.extype = raw_term::REL;
				rt677.e.push_back(e676);
				rt677.e.push_back(e1);
				rt677.e.push_back(e210);
				rt677.e.push_back(e211);
				rt677.e.push_back(e162);
				rt677.e.push_back(e39);
				rt677.e.push_back(e3);
				rt677.calc_arity(nullptr);
				sprawformtree ft675 = std::make_shared<raw_form_tree>(elem::NONE, rt677);
				sprawformtree ft673 = std::make_shared<raw_form_tree>(elem::EXISTS, ft674, ft675);
				sprawformtree ft671 = std::make_shared<raw_form_tree>(elem::EXISTS, ft672, ft673);
				sprawformtree ft670 = std::make_shared<raw_form_tree>(elem::NOT, ft671);
				sprawformtree ft661 = std::make_shared<raw_form_tree>(elem::AND, ft662, ft670);
				raw_rule rr678;
				rr678.h.push_back(rt660);
				rr678.set_prft(ft661);
				raw_term rt679;
				rt679.neg = false;
				rt679.extype = raw_term::REL;
				rt679.e.push_back(e559);
				rt679.e.push_back(e1);
				rt679.e.push_back(e212);
				rt679.e.push_back(e218);
				rt679.e.push_back(e59);
				rt679.e.push_back(e47);
				rt679.e.push_back(e3);
				rt679.calc_arity(nullptr);
				elem e680;
				e680.type = elem::SYM;
				e680.e = d.get_lexeme("IS_DICT_CONSISTENT1");
				raw_term rt681;
				rt681.neg = false;
				rt681.extype = raw_term::REL;
				rt681.e.push_back(e680);
				rt681.e.push_back(e1);
				rt681.e.push_back(e210);
				rt681.e.push_back(e211);
				rt681.e.push_back(e195);
				rt681.e.push_back(e196);
				rt681.e.push_back(e3);
				rt681.calc_arity(nullptr);
				raw_term rt687;
				rt687.neg = false;
				rt687.extype = raw_term::REL;
				rt687.e.push_back(e659);
				rt687.e.push_back(e1);
				rt687.e.push_back(e210);
				rt687.e.push_back(e211);
				rt687.e.push_back(e195);
				rt687.e.push_back(e196);
				rt687.e.push_back(e3);
				rt687.calc_arity(nullptr);
				sprawformtree ft686 = std::make_shared<raw_form_tree>(elem::NONE, rt687);
				raw_term rt689;
				rt689.neg = false;
				rt689.extype = raw_term::REL;
				rt689.e.push_back(e153);
				rt689.e.push_back(e1);
				rt689.e.push_back(e195);
				rt689.e.push_back(e59);
				rt689.e.push_back(e212);
				rt689.e.push_back(e3);
				rt689.calc_arity(nullptr);
				sprawformtree ft688 = std::make_shared<raw_form_tree>(elem::NONE, rt689);
				sprawformtree ft685 = std::make_shared<raw_form_tree>(elem::AND, ft686, ft688);
				raw_term rt691;
				rt691.neg = false;
				rt691.extype = raw_term::REL;
				rt691.e.push_back(e153);
				rt691.e.push_back(e1);
				rt691.e.push_back(e196);
				rt691.e.push_back(e47);
				rt691.e.push_back(e218);
				rt691.e.push_back(e3);
				rt691.calc_arity(nullptr);
				sprawformtree ft690 = std::make_shared<raw_form_tree>(elem::NONE, rt691);
				sprawformtree ft684 = std::make_shared<raw_form_tree>(elem::AND, ft685, ft690);
				raw_term rt694;
				rt694.neg = false;
				rt694.extype = raw_term::REL;
				rt694.e.push_back(e668);
				rt694.e.push_back(e1);
				rt694.e.push_back(e210);
				rt694.e.push_back(e211);
				rt694.e.push_back(e3);
				rt694.calc_arity(nullptr);
				sprawformtree ft693 = std::make_shared<raw_form_tree>(elem::NONE, rt694);
				sprawformtree ft692 = std::make_shared<raw_form_tree>(elem::NOT, ft693);
				sprawformtree ft683 = std::make_shared<raw_form_tree>(elem::AND, ft684, ft692);
				sprawformtree ft697 = std::make_shared<raw_form_tree>(elem::VAR, e162);
				sprawformtree ft699 = std::make_shared<raw_form_tree>(elem::VAR, e39);
				raw_term rt701;
				rt701.neg = false;
				rt701.extype = raw_term::REL;
				rt701.e.push_back(e676);
				rt701.e.push_back(e1);
				rt701.e.push_back(e210);
				rt701.e.push_back(e211);
				rt701.e.push_back(e162);
				rt701.e.push_back(e39);
				rt701.e.push_back(e3);
				rt701.calc_arity(nullptr);
				sprawformtree ft700 = std::make_shared<raw_form_tree>(elem::NONE, rt701);
				sprawformtree ft698 = std::make_shared<raw_form_tree>(elem::EXISTS, ft699, ft700);
				sprawformtree ft696 = std::make_shared<raw_form_tree>(elem::EXISTS, ft697, ft698);
				sprawformtree ft695 = std::make_shared<raw_form_tree>(elem::NOT, ft696);
				sprawformtree ft682 = std::make_shared<raw_form_tree>(elem::AND, ft683, ft695);
				raw_rule rr702;
				rr702.h.push_back(rt679);
				rr702.h.push_back(rt681);
				rr702.set_prft(ft682);
				raw_term rt703;
				rt703.neg = false;
				rt703.extype = raw_term::REL;
				rt703.e.push_back(e659);
				rt703.e.push_back(e1);
				rt703.e.push_back(e210);
				rt703.e.push_back(e211);
				rt703.e.push_back(e212);
				rt703.e.push_back(e218);
				rt703.e.push_back(e3);
				rt703.calc_arity(nullptr);
				raw_term rt710;
				rt710.neg = false;
				rt710.extype = raw_term::REL;
				rt710.e.push_back(e563);
				rt710.e.push_back(e1);
				rt710.e.push_back(e212);
				rt710.e.push_back(e218);
				rt710.e.push_back(e59);
				rt710.e.push_back(e47);
				rt710.e.push_back(e3);
				rt710.calc_arity(nullptr);
				sprawformtree ft709 = std::make_shared<raw_form_tree>(elem::NONE, rt710);
				raw_term rt712;
				rt712.neg = false;
				rt712.extype = raw_term::REL;
				rt712.e.push_back(e680);
				rt712.e.push_back(e1);
				rt712.e.push_back(e210);
				rt712.e.push_back(e211);
				rt712.e.push_back(e195);
				rt712.e.push_back(e196);
				rt712.e.push_back(e3);
				rt712.calc_arity(nullptr);
				sprawformtree ft711 = std::make_shared<raw_form_tree>(elem::NONE, rt712);
				sprawformtree ft708 = std::make_shared<raw_form_tree>(elem::AND, ft709, ft711);
				raw_term rt714;
				rt714.neg = false;
				rt714.extype = raw_term::REL;
				rt714.e.push_back(e153);
				rt714.e.push_back(e1);
				rt714.e.push_back(e195);
				rt714.e.push_back(e59);
				rt714.e.push_back(e212);
				rt714.e.push_back(e3);
				rt714.calc_arity(nullptr);
				sprawformtree ft713 = std::make_shared<raw_form_tree>(elem::NONE, rt714);
				sprawformtree ft707 = std::make_shared<raw_form_tree>(elem::AND, ft708, ft713);
				raw_term rt716;
				rt716.neg = false;
				rt716.extype = raw_term::REL;
				rt716.e.push_back(e153);
				rt716.e.push_back(e1);
				rt716.e.push_back(e196);
				rt716.e.push_back(e47);
				rt716.e.push_back(e218);
				rt716.e.push_back(e3);
				rt716.calc_arity(nullptr);
				sprawformtree ft715 = std::make_shared<raw_form_tree>(elem::NONE, rt716);
				sprawformtree ft706 = std::make_shared<raw_form_tree>(elem::AND, ft707, ft715);
				raw_term rt719;
				rt719.neg = false;
				rt719.extype = raw_term::REL;
				rt719.e.push_back(e668);
				rt719.e.push_back(e1);
				rt719.e.push_back(e210);
				rt719.e.push_back(e211);
				rt719.e.push_back(e3);
				rt719.calc_arity(nullptr);
				sprawformtree ft718 = std::make_shared<raw_form_tree>(elem::NONE, rt719);
				sprawformtree ft717 = std::make_shared<raw_form_tree>(elem::NOT, ft718);
				sprawformtree ft705 = std::make_shared<raw_form_tree>(elem::AND, ft706, ft717);
				sprawformtree ft722 = std::make_shared<raw_form_tree>(elem::VAR, e162);
				sprawformtree ft724 = std::make_shared<raw_form_tree>(elem::VAR, e39);
				raw_term rt726;
				rt726.neg = false;
				rt726.extype = raw_term::REL;
				rt726.e.push_back(e676);
				rt726.e.push_back(e1);
				rt726.e.push_back(e210);
				rt726.e.push_back(e211);
				rt726.e.push_back(e162);
				rt726.e.push_back(e39);
				rt726.e.push_back(e3);
				rt726.calc_arity(nullptr);
				sprawformtree ft725 = std::make_shared<raw_form_tree>(elem::NONE, rt726);
				sprawformtree ft723 = std::make_shared<raw_form_tree>(elem::EXISTS, ft724, ft725);
				sprawformtree ft721 = std::make_shared<raw_form_tree>(elem::EXISTS, ft722, ft723);
				sprawformtree ft720 = std::make_shared<raw_form_tree>(elem::NOT, ft721);
				sprawformtree ft704 = std::make_shared<raw_form_tree>(elem::AND, ft705, ft720);
				raw_rule rr727;
				rr727.h.push_back(rt703);
				rr727.set_prft(ft704);
				raw_term rt728;
				rt728.neg = false;
				rt728.extype = raw_term::REL;
				rt728.e.push_back(e676);
				rt728.e.push_back(e1);
				rt728.e.push_back(e210);
				rt728.e.push_back(e211);
				rt728.e.push_back(e212);
				rt728.e.push_back(e218);
				rt728.e.push_back(e3);
				rt728.calc_arity(nullptr);
				raw_term rt735;
				rt735.neg = false;
				rt735.extype = raw_term::REL;
				rt735.e.push_back(e567);
				rt735.e.push_back(e1);
				rt735.e.push_back(e212);
				rt735.e.push_back(e218);
				rt735.e.push_back(e59);
				rt735.e.push_back(e47);
				rt735.e.push_back(e3);
				rt735.calc_arity(nullptr);
				sprawformtree ft734 = std::make_shared<raw_form_tree>(elem::NONE, rt735);
				raw_term rt737;
				rt737.neg = false;
				rt737.extype = raw_term::REL;
				rt737.e.push_back(e680);
				rt737.e.push_back(e1);
				rt737.e.push_back(e210);
				rt737.e.push_back(e211);
				rt737.e.push_back(e195);
				rt737.e.push_back(e196);
				rt737.e.push_back(e3);
				rt737.calc_arity(nullptr);
				sprawformtree ft736 = std::make_shared<raw_form_tree>(elem::NONE, rt737);
				sprawformtree ft733 = std::make_shared<raw_form_tree>(elem::AND, ft734, ft736);
				raw_term rt739;
				rt739.neg = false;
				rt739.extype = raw_term::REL;
				rt739.e.push_back(e153);
				rt739.e.push_back(e1);
				rt739.e.push_back(e195);
				rt739.e.push_back(e59);
				rt739.e.push_back(e212);
				rt739.e.push_back(e3);
				rt739.calc_arity(nullptr);
				sprawformtree ft738 = std::make_shared<raw_form_tree>(elem::NONE, rt739);
				sprawformtree ft732 = std::make_shared<raw_form_tree>(elem::AND, ft733, ft738);
				raw_term rt741;
				rt741.neg = false;
				rt741.extype = raw_term::REL;
				rt741.e.push_back(e153);
				rt741.e.push_back(e1);
				rt741.e.push_back(e196);
				rt741.e.push_back(e47);
				rt741.e.push_back(e218);
				rt741.e.push_back(e3);
				rt741.calc_arity(nullptr);
				sprawformtree ft740 = std::make_shared<raw_form_tree>(elem::NONE, rt741);
				sprawformtree ft731 = std::make_shared<raw_form_tree>(elem::AND, ft732, ft740);
				raw_term rt744;
				rt744.neg = false;
				rt744.extype = raw_term::REL;
				rt744.e.push_back(e668);
				rt744.e.push_back(e1);
				rt744.e.push_back(e210);
				rt744.e.push_back(e211);
				rt744.e.push_back(e3);
				rt744.calc_arity(nullptr);
				sprawformtree ft743 = std::make_shared<raw_form_tree>(elem::NONE, rt744);
				sprawformtree ft742 = std::make_shared<raw_form_tree>(elem::NOT, ft743);
				sprawformtree ft730 = std::make_shared<raw_form_tree>(elem::AND, ft731, ft742);
				sprawformtree ft747 = std::make_shared<raw_form_tree>(elem::VAR, e162);
				sprawformtree ft749 = std::make_shared<raw_form_tree>(elem::VAR, e39);
				raw_term rt751;
				rt751.neg = false;
				rt751.extype = raw_term::REL;
				rt751.e.push_back(e676);
				rt751.e.push_back(e1);
				rt751.e.push_back(e210);
				rt751.e.push_back(e211);
				rt751.e.push_back(e162);
				rt751.e.push_back(e39);
				rt751.e.push_back(e3);
				rt751.calc_arity(nullptr);
				sprawformtree ft750 = std::make_shared<raw_form_tree>(elem::NONE, rt751);
				sprawformtree ft748 = std::make_shared<raw_form_tree>(elem::EXISTS, ft749, ft750);
				sprawformtree ft746 = std::make_shared<raw_form_tree>(elem::EXISTS, ft747, ft748);
				sprawformtree ft745 = std::make_shared<raw_form_tree>(elem::NOT, ft746);
				sprawformtree ft729 = std::make_shared<raw_form_tree>(elem::AND, ft730, ft745);
				raw_rule rr752;
				rr752.h.push_back(rt728);
				rr752.set_prft(ft729);
				raw_term rt753;
				rt753.neg = false;
				rt753.extype = raw_term::REL;
				rt753.e.push_back(e668);
				rt753.e.push_back(e1);
				rt753.e.push_back(e210);
				rt753.e.push_back(e211);
				rt753.e.push_back(e3);
				rt753.calc_arity(nullptr);
				raw_term rt759;
				rt759.neg = false;
				rt759.extype = raw_term::REL;
				rt759.e.push_back(e659);
				rt759.e.push_back(e1);
				rt759.e.push_back(e210);
				rt759.e.push_back(e211);
				rt759.e.push_back(e195);
				rt759.e.push_back(e196);
				rt759.e.push_back(e3);
				rt759.calc_arity(nullptr);
				sprawformtree ft758 = std::make_shared<raw_form_tree>(elem::NONE, rt759);
				raw_term rt761;
				rt761.neg = false;
				rt761.extype = raw_term::REL;
				rt761.e.push_back(e153);
				rt761.e.push_back(e1);
				rt761.e.push_back(e195);
				rt761.e.push_back(e3);
				rt761.calc_arity(nullptr);
				sprawformtree ft760 = std::make_shared<raw_form_tree>(elem::NONE, rt761);
				sprawformtree ft757 = std::make_shared<raw_form_tree>(elem::AND, ft758, ft760);
				raw_term rt763;
				rt763.neg = false;
				rt763.extype = raw_term::REL;
				rt763.e.push_back(e153);
				rt763.e.push_back(e1);
				rt763.e.push_back(e196);
				rt763.e.push_back(e3);
				rt763.calc_arity(nullptr);
				sprawformtree ft762 = std::make_shared<raw_form_tree>(elem::NONE, rt763);
				sprawformtree ft756 = std::make_shared<raw_form_tree>(elem::AND, ft757, ft762);
				raw_term rt766;
				rt766.neg = false;
				rt766.extype = raw_term::REL;
				rt766.e.push_back(e668);
				rt766.e.push_back(e1);
				rt766.e.push_back(e210);
				rt766.e.push_back(e211);
				rt766.e.push_back(e3);
				rt766.calc_arity(nullptr);
				sprawformtree ft765 = std::make_shared<raw_form_tree>(elem::NONE, rt766);
				sprawformtree ft764 = std::make_shared<raw_form_tree>(elem::NOT, ft765);
				sprawformtree ft755 = std::make_shared<raw_form_tree>(elem::AND, ft756, ft764);
				sprawformtree ft769 = std::make_shared<raw_form_tree>(elem::VAR, e162);
				sprawformtree ft771 = std::make_shared<raw_form_tree>(elem::VAR, e39);
				raw_term rt773;
				rt773.neg = false;
				rt773.extype = raw_term::REL;
				rt773.e.push_back(e676);
				rt773.e.push_back(e1);
				rt773.e.push_back(e210);
				rt773.e.push_back(e211);
				rt773.e.push_back(e162);
				rt773.e.push_back(e39);
				rt773.e.push_back(e3);
				rt773.calc_arity(nullptr);
				sprawformtree ft772 = std::make_shared<raw_form_tree>(elem::NONE, rt773);
				sprawformtree ft770 = std::make_shared<raw_form_tree>(elem::EXISTS, ft771, ft772);
				sprawformtree ft768 = std::make_shared<raw_form_tree>(elem::EXISTS, ft769, ft770);
				sprawformtree ft767 = std::make_shared<raw_form_tree>(elem::NOT, ft768);
				sprawformtree ft754 = std::make_shared<raw_form_tree>(elem::AND, ft755, ft767);
				raw_rule rr774;
				rr774.h.push_back(rt753);
				rr774.set_prft(ft754);
				raw_term rt775;
				rt775.neg = true;
				rt775.extype = raw_term::REL;
				rt775.e.push_back(e659);
				rt775.e.push_back(e1);
				rt775.e.push_back(e210);
				rt775.e.push_back(e211);
				rt775.e.push_back(e195);
				rt775.e.push_back(e196);
				rt775.e.push_back(e3);
				rt775.calc_arity(nullptr);
				raw_term rt776;
				rt776.neg = true;
				rt776.extype = raw_term::REL;
				rt776.e.push_back(e680);
				rt776.e.push_back(e1);
				rt776.e.push_back(e210);
				rt776.e.push_back(e211);
				rt776.e.push_back(e195);
				rt776.e.push_back(e196);
				rt776.e.push_back(e3);
				rt776.calc_arity(nullptr);
				raw_term rt779;
				rt779.neg = false;
				rt779.extype = raw_term::REL;
				rt779.e.push_back(e668);
				rt779.e.push_back(e1);
				rt779.e.push_back(e210);
				rt779.e.push_back(e211);
				rt779.e.push_back(e3);
				rt779.calc_arity(nullptr);
				sprawformtree ft778 = std::make_shared<raw_form_tree>(elem::NONE, rt779);
				elem e781;
				e781.type = elem::VAR;
				e781.e = d.get_lexeme("?axs");
				elem e782;
				e782.type = elem::VAR;
				e782.e = d.get_lexeme("?ays");
				raw_term rt783;
				rt783.neg = false;
				rt783.extype = raw_term::REL;
				rt783.e.push_back(e676);
				rt783.e.push_back(e1);
				rt783.e.push_back(e210);
				rt783.e.push_back(e211);
				rt783.e.push_back(e781);
				rt783.e.push_back(e782);
				rt783.e.push_back(e3);
				rt783.calc_arity(nullptr);
				sprawformtree ft780 = std::make_shared<raw_form_tree>(elem::NONE, rt783);
				sprawformtree ft777 = std::make_shared<raw_form_tree>(elem::ALT, ft778, ft780);
				raw_rule rr784;
				rr784.h.push_back(rt775);
				rr784.h.push_back(rt776);
				rr784.set_prft(ft777);
				elem e785;
				e785.type = elem::SYM;
				e785.e = d.get_lexeme("DO_FIX_SYMS0");
				raw_term rt786;
				rt786.neg = false;
				rt786.extype = raw_term::REL;
				rt786.e.push_back(e785);
				rt786.e.push_back(e1);
				rt786.e.push_back(e236);
				rt786.e.push_back(e236);
				rt786.e.push_back(e251);
				rt786.e.push_back(e3);
				rt786.calc_arity(nullptr);
				elem e790;
				e790.type = elem::SYM;
				e790.e = d.get_lexeme("DO_FIX_SYMS");
				raw_term rt791;
				rt791.neg = false;
				rt791.extype = raw_term::REL;
				rt791.e.push_back(e790);
				rt791.e.push_back(e1);
				rt791.e.push_back(e236);
				rt791.e.push_back(e3);
				rt791.calc_arity(nullptr);
				sprawformtree ft789 = std::make_shared<raw_form_tree>(elem::NONE, rt791);
				raw_term rt793;
				rt793.neg = false;
				rt793.extype = raw_term::REL;
				rt793.e.push_back(e153);
				rt793.e.push_back(e1);
				rt793.e.push_back(e251);
				rt793.e.push_back(e3);
				rt793.calc_arity(nullptr);
				sprawformtree ft792 = std::make_shared<raw_form_tree>(elem::NONE, rt793);
				sprawformtree ft788 = std::make_shared<raw_form_tree>(elem::AND, ft789, ft792);
				sprawformtree ft796 = std::make_shared<raw_form_tree>(elem::VAR, e162);
				elem e798;
				e798.type = elem::SYM;
				e798.e = d.get_lexeme("FIX_SYMS");
				raw_term rt799;
				rt799.neg = false;
				rt799.extype = raw_term::REL;
				rt799.e.push_back(e798);
				rt799.e.push_back(e1);
				rt799.e.push_back(e236);
				rt799.e.push_back(e162);
				rt799.e.push_back(e3);
				rt799.calc_arity(nullptr);
				sprawformtree ft797 = std::make_shared<raw_form_tree>(elem::NONE, rt799);
				sprawformtree ft795 = std::make_shared<raw_form_tree>(elem::EXISTS, ft796, ft797);
				sprawformtree ft794 = std::make_shared<raw_form_tree>(elem::NOT, ft795);
				sprawformtree ft787 = std::make_shared<raw_form_tree>(elem::AND, ft788, ft794);
				raw_rule rr800;
				rr800.h.push_back(rt786);
				rr800.set_prft(ft787);
				elem e801;
				e801.type = elem::VAR;
				e801.e = d.get_lexeme("?oas");
				raw_term rt802;
				rt802.neg = false;
				rt802.extype = raw_term::REL;
				rt802.e.push_back(e785);
				rt802.e.push_back(e1);
				rt802.e.push_back(e801);
				rt802.e.push_back(e273);
				rt802.e.push_back(e251);
				rt802.e.push_back(e3);
				rt802.calc_arity(nullptr);
				elem e808;
				e808.type = elem::VAR;
				e808.e = d.get_lexeme("?bs_tl");
				raw_term rt809;
				rt809.neg = false;
				rt809.extype = raw_term::REL;
				rt809.e.push_back(e785);
				rt809.e.push_back(e1);
				rt809.e.push_back(e801);
				rt809.e.push_back(e236);
				rt809.e.push_back(e808);
				rt809.e.push_back(e3);
				rt809.calc_arity(nullptr);
				sprawformtree ft807 = std::make_shared<raw_form_tree>(elem::NONE, rt809);
				raw_term rt811;
				rt811.neg = false;
				rt811.extype = raw_term::REL;
				rt811.e.push_back(e153);
				rt811.e.push_back(e1);
				rt811.e.push_back(e236);
				rt811.e.push_back(e272);
				rt811.e.push_back(e273);
				rt811.e.push_back(e3);
				rt811.calc_arity(nullptr);
				sprawformtree ft810 = std::make_shared<raw_form_tree>(elem::NONE, rt811);
				sprawformtree ft806 = std::make_shared<raw_form_tree>(elem::AND, ft807, ft810);
				elem e815;
				e815.type = elem::SYM;
				e815.e = d.get_lexeme("VARS");
				raw_term rt816;
				rt816.neg = false;
				rt816.extype = raw_term::REL;
				rt816.e.push_back(e6);
				rt816.e.push_back(e1);
				rt816.e.push_back(e815);
				rt816.e.push_back(e272);
				rt816.e.push_back(e3);
				rt816.calc_arity(nullptr);
				sprawformtree ft814 = std::make_shared<raw_form_tree>(elem::NONE, rt816);
				elem e818;
				e818.type = elem::VAR;
				e818.e = d.get_lexeme("?bs_hd");
				raw_term rt819;
				rt819.neg = false;
				rt819.extype = raw_term::REL;
				rt819.e.push_back(e150);
				rt819.e.push_back(e1);
				rt819.e.push_back(e818);
				rt819.e.push_back(e3);
				rt819.calc_arity(nullptr);
				sprawformtree ft817 = std::make_shared<raw_form_tree>(elem::NONE, rt819);
				sprawformtree ft813 = std::make_shared<raw_form_tree>(elem::AND, ft814, ft817);
				elem e822;
				e822.type = elem::SYM;
				e822.e = d.get_lexeme("SYM");
				raw_term rt823;
				rt823.neg = false;
				rt823.extype = raw_term::REL;
				rt823.e.push_back(e6);
				rt823.e.push_back(e1);
				rt823.e.push_back(e822);
				rt823.e.push_back(e272);
				rt823.e.push_back(e3);
				rt823.calc_arity(nullptr);
				sprawformtree ft821 = std::make_shared<raw_form_tree>(elem::NONE, rt823);
				raw_term rt825;
				rt825.neg = false;
				rt825.extype = raw_term::EQ;
				rt825.e.push_back(e272);
				rt825.e.push_back(e109);
				rt825.e.push_back(e818);
				rt825.calc_arity(nullptr);
				sprawformtree ft824 = std::make_shared<raw_form_tree>(elem::NONE, rt825);
				sprawformtree ft820 = std::make_shared<raw_form_tree>(elem::AND, ft821, ft824);
				sprawformtree ft812 = std::make_shared<raw_form_tree>(elem::ALT, ft813, ft820);
				sprawformtree ft805 = std::make_shared<raw_form_tree>(elem::AND, ft806, ft812);
				raw_term rt827;
				rt827.neg = false;
				rt827.extype = raw_term::REL;
				rt827.e.push_back(e153);
				rt827.e.push_back(e1);
				rt827.e.push_back(e251);
				rt827.e.push_back(e818);
				rt827.e.push_back(e808);
				rt827.e.push_back(e3);
				rt827.calc_arity(nullptr);
				sprawformtree ft826 = std::make_shared<raw_form_tree>(elem::NONE, rt827);
				sprawformtree ft804 = std::make_shared<raw_form_tree>(elem::AND, ft805, ft826);
				sprawformtree ft830 = std::make_shared<raw_form_tree>(elem::VAR, e162);
				raw_term rt832;
				rt832.neg = false;
				rt832.extype = raw_term::REL;
				rt832.e.push_back(e798);
				rt832.e.push_back(e1);
				rt832.e.push_back(e801);
				rt832.e.push_back(e162);
				rt832.e.push_back(e3);
				rt832.calc_arity(nullptr);
				sprawformtree ft831 = std::make_shared<raw_form_tree>(elem::NONE, rt832);
				sprawformtree ft829 = std::make_shared<raw_form_tree>(elem::EXISTS, ft830, ft831);
				sprawformtree ft828 = std::make_shared<raw_form_tree>(elem::NOT, ft829);
				sprawformtree ft803 = std::make_shared<raw_form_tree>(elem::AND, ft804, ft828);
				raw_rule rr833;
				rr833.h.push_back(rt802);
				rr833.set_prft(ft803);
				raw_term rt834;
				rt834.neg = false;
				rt834.extype = raw_term::REL;
				rt834.e.push_back(e250);
				rt834.e.push_back(e1);
				rt834.e.push_back(e251);
				rt834.e.push_back(e3);
				rt834.calc_arity(nullptr);
				elem e835;
				e835.type = elem::SYM;
				e835.e = d.get_lexeme("DO_FIX_SYMS1");
				raw_term rt836;
				rt836.neg = false;
				rt836.extype = raw_term::REL;
				rt836.e.push_back(e835);
				rt836.e.push_back(e1);
				rt836.e.push_back(e801);
				rt836.e.push_back(e251);
				rt836.e.push_back(e3);
				rt836.calc_arity(nullptr);
				raw_term rt840;
				rt840.neg = false;
				rt840.extype = raw_term::REL;
				rt840.e.push_back(e785);
				rt840.e.push_back(e1);
				rt840.e.push_back(e801);
				rt840.e.push_back(e236);
				rt840.e.push_back(e251);
				rt840.e.push_back(e3);
				rt840.calc_arity(nullptr);
				sprawformtree ft839 = std::make_shared<raw_form_tree>(elem::NONE, rt840);
				raw_term rt842;
				rt842.neg = false;
				rt842.extype = raw_term::REL;
				rt842.e.push_back(e153);
				rt842.e.push_back(e1);
				rt842.e.push_back(e236);
				rt842.e.push_back(e3);
				rt842.calc_arity(nullptr);
				sprawformtree ft841 = std::make_shared<raw_form_tree>(elem::NONE, rt842);
				sprawformtree ft838 = std::make_shared<raw_form_tree>(elem::AND, ft839, ft841);
				sprawformtree ft845 = std::make_shared<raw_form_tree>(elem::VAR, e162);
				raw_term rt847;
				rt847.neg = false;
				rt847.extype = raw_term::REL;
				rt847.e.push_back(e798);
				rt847.e.push_back(e1);
				rt847.e.push_back(e801);
				rt847.e.push_back(e162);
				rt847.e.push_back(e3);
				rt847.calc_arity(nullptr);
				sprawformtree ft846 = std::make_shared<raw_form_tree>(elem::NONE, rt847);
				sprawformtree ft844 = std::make_shared<raw_form_tree>(elem::EXISTS, ft845, ft846);
				sprawformtree ft843 = std::make_shared<raw_form_tree>(elem::NOT, ft844);
				sprawformtree ft837 = std::make_shared<raw_form_tree>(elem::AND, ft838, ft843);
				raw_rule rr848;
				rr848.h.push_back(rt834);
				rr848.h.push_back(rt836);
				rr848.set_prft(ft837);
				raw_term rt849;
				rt849.neg = false;
				rt849.extype = raw_term::REL;
				rt849.e.push_back(e798);
				rt849.e.push_back(e1);
				rt849.e.push_back(e236);
				rt849.e.push_back(e251);
				rt849.e.push_back(e3);
				rt849.calc_arity(nullptr);
				raw_term rt852;
				rt852.neg = false;
				rt852.extype = raw_term::REL;
				rt852.e.push_back(e835);
				rt852.e.push_back(e1);
				rt852.e.push_back(e236);
				rt852.e.push_back(e205);
				rt852.e.push_back(e3);
				rt852.calc_arity(nullptr);
				sprawformtree ft851 = std::make_shared<raw_form_tree>(elem::NONE, rt852);
				raw_term rt854;
				rt854.neg = false;
				rt854.extype = raw_term::REL;
				rt854.e.push_back(e263);
				rt854.e.push_back(e1);
				rt854.e.push_back(e205);
				rt854.e.push_back(e251);
				rt854.e.push_back(e3);
				rt854.calc_arity(nullptr);
				sprawformtree ft853 = std::make_shared<raw_form_tree>(elem::NONE, rt854);
				sprawformtree ft850 = std::make_shared<raw_form_tree>(elem::AND, ft851, ft853);
				raw_rule rr855;
				rr855.h.push_back(rt849);
				rr855.set_prft(ft850);
				raw_term rt856;
				rt856.neg = true;
				rt856.extype = raw_term::REL;
				rt856.e.push_back(e785);
				rt856.e.push_back(e1);
				rt856.e.push_back(e801);
				rt856.e.push_back(e236);
				rt856.e.push_back(e251);
				rt856.e.push_back(e3);
				rt856.calc_arity(nullptr);
				raw_term rt857;
				rt857.neg = true;
				rt857.extype = raw_term::REL;
				rt857.e.push_back(e835);
				rt857.e.push_back(e1);
				rt857.e.push_back(e801);
				rt857.e.push_back(e251);
				rt857.e.push_back(e3);
				rt857.calc_arity(nullptr);
				raw_term rt859;
				rt859.neg = false;
				rt859.extype = raw_term::REL;
				rt859.e.push_back(e798);
				rt859.e.push_back(e1);
				rt859.e.push_back(e801);
				rt859.e.push_back(e162);
				rt859.e.push_back(e3);
				rt859.calc_arity(nullptr);
				sprawformtree ft858 = std::make_shared<raw_form_tree>(elem::NONE, rt859);
				raw_rule rr860;
				rr860.h.push_back(rt856);
				rr860.h.push_back(rt857);
				rr860.set_prft(ft858);
				raw_term rt861;
				rt861.neg = false;
				rt861.extype = raw_term::REL;
				rt861.e.push_back(e46);
				rt861.e.push_back(e1);
				rt861.e.push_back(e2);
				rt861.e.push_back(e3);
				rt861.calc_arity(nullptr);
				elem e867;
				e867.type = elem::VAR;
				e867.e = d.get_lexeme("?e0");
				elem e868;
				e868.type = elem::VAR;
				e868.e = d.get_lexeme("?e1");
				raw_term rt869;
				rt869.neg = false;
				rt869.extype = raw_term::REL;
				rt869.e.push_back(e6);
				rt869.e.push_back(e1);
				rt869.e.push_back(e37);
				rt869.e.push_back(e2);
				rt869.e.push_back(e867);
				rt869.e.push_back(e868);
				rt869.e.push_back(e3);
				rt869.calc_arity(nullptr);
				sprawformtree ft866 = std::make_shared<raw_form_tree>(elem::NONE, rt869);
				elem e871;
				e871.type = elem::VAR;
				e871.e = d.get_lexeme("?nm");
				raw_term rt872;
				rt872.neg = false;
				rt872.extype = raw_term::REL;
				rt872.e.push_back(e6);
				rt872.e.push_back(e1);
				rt872.e.push_back(e7);
				rt872.e.push_back(e867);
				rt872.e.push_back(e871);
				rt872.e.push_back(e205);
				rt872.e.push_back(e3);
				rt872.calc_arity(nullptr);
				sprawformtree ft870 = std::make_shared<raw_form_tree>(elem::NONE, rt872);
				sprawformtree ft865 = std::make_shared<raw_form_tree>(elem::AND, ft866, ft870);
				sprawformtree ft875 = std::make_shared<raw_form_tree>(elem::VAR, e236);
				sprawformtree ft877 = std::make_shared<raw_form_tree>(elem::VAR, e251);
				elem e879;
				e879.type = elem::SYM;
				e879.e = d.get_lexeme("FORMULA_OUT");
				raw_term rt880;
				rt880.neg = false;
				rt880.extype = raw_term::REL;
				rt880.e.push_back(e879);
				rt880.e.push_back(e1);
				rt880.e.push_back(e868);
				rt880.e.push_back(e236);
				rt880.e.push_back(e251);
				rt880.e.push_back(e3);
				rt880.calc_arity(nullptr);
				sprawformtree ft878 = std::make_shared<raw_form_tree>(elem::NONE, rt880);
				sprawformtree ft876 = std::make_shared<raw_form_tree>(elem::EXISTS, ft877, ft878);
				sprawformtree ft874 = std::make_shared<raw_form_tree>(elem::EXISTS, ft875, ft876);
				sprawformtree ft873 = std::make_shared<raw_form_tree>(elem::NOT, ft874);
				sprawformtree ft864 = std::make_shared<raw_form_tree>(elem::AND, ft865, ft873);
				raw_term rt882;
				rt882.neg = false;
				rt882.extype = raw_term::REL;
				rt882.e.push_back(e42);
				rt882.e.push_back(e1);
				rt882.e.push_back(e3);
				rt882.calc_arity(nullptr);
				sprawformtree ft881 = std::make_shared<raw_form_tree>(elem::NONE, rt882);
				sprawformtree ft863 = std::make_shared<raw_form_tree>(elem::AND, ft864, ft881);
				raw_term rt885;
				rt885.neg = false;
				rt885.extype = raw_term::REL;
				rt885.e.push_back(e70);
				rt885.e.push_back(e1);
				rt885.e.push_back(e3);
				rt885.calc_arity(nullptr);
				sprawformtree ft884 = std::make_shared<raw_form_tree>(elem::NONE, rt885);
				sprawformtree ft883 = std::make_shared<raw_form_tree>(elem::NOT, ft884);
				sprawformtree ft862 = std::make_shared<raw_form_tree>(elem::AND, ft863, ft883);
				raw_rule rr886;
				rr886.h.push_back(rt861);
				rr886.set_prft(ft862);
				raw_term rt887;
				rt887.neg = false;
				rt887.extype = raw_term::REL;
				rt887.e.push_back(e468);
				rt887.e.push_back(e1);
				rt887.e.push_back(e236);
				rt887.e.push_back(e251);
				rt887.e.push_back(e205);
				rt887.e.push_back(e3);
				rt887.calc_arity(nullptr);
				raw_term rt888;
				rt888.neg = false;
				rt888.extype = raw_term::REL;
				rt888.e.push_back(e664);
				rt888.e.push_back(e1);
				rt888.e.push_back(e236);
				rt888.e.push_back(e251);
				rt888.e.push_back(e3);
				rt888.calc_arity(nullptr);
				raw_term rt889;
				rt889.neg = false;
				rt889.extype = raw_term::REL;
				rt889.e.push_back(e790);
				rt889.e.push_back(e1);
				rt889.e.push_back(e205);
				rt889.e.push_back(e3);
				rt889.calc_arity(nullptr);
				raw_term rt895;
				rt895.neg = false;
				rt895.extype = raw_term::REL;
				rt895.e.push_back(e6);
				rt895.e.push_back(e1);
				rt895.e.push_back(e37);
				rt895.e.push_back(e2);
				rt895.e.push_back(e867);
				rt895.e.push_back(e868);
				rt895.e.push_back(e3);
				rt895.calc_arity(nullptr);
				sprawformtree ft894 = std::make_shared<raw_form_tree>(elem::NONE, rt895);
				raw_term rt897;
				rt897.neg = false;
				rt897.extype = raw_term::REL;
				rt897.e.push_back(e6);
				rt897.e.push_back(e1);
				rt897.e.push_back(e7);
				rt897.e.push_back(e867);
				rt897.e.push_back(e871);
				rt897.e.push_back(e205);
				rt897.e.push_back(e3);
				rt897.calc_arity(nullptr);
				sprawformtree ft896 = std::make_shared<raw_form_tree>(elem::NONE, rt897);
				sprawformtree ft893 = std::make_shared<raw_form_tree>(elem::AND, ft894, ft896);
				raw_term rt899;
				rt899.neg = false;
				rt899.extype = raw_term::REL;
				rt899.e.push_back(e879);
				rt899.e.push_back(e1);
				rt899.e.push_back(e868);
				rt899.e.push_back(e236);
				rt899.e.push_back(e251);
				rt899.e.push_back(e3);
				rt899.calc_arity(nullptr);
				sprawformtree ft898 = std::make_shared<raw_form_tree>(elem::NONE, rt899);
				sprawformtree ft892 = std::make_shared<raw_form_tree>(elem::AND, ft893, ft898);
				raw_term rt901;
				rt901.neg = false;
				rt901.extype = raw_term::REL;
				rt901.e.push_back(e42);
				rt901.e.push_back(e1);
				rt901.e.push_back(e3);
				rt901.calc_arity(nullptr);
				sprawformtree ft900 = std::make_shared<raw_form_tree>(elem::NONE, rt901);
				sprawformtree ft891 = std::make_shared<raw_form_tree>(elem::AND, ft892, ft900);
				raw_term rt904;
				rt904.neg = false;
				rt904.extype = raw_term::REL;
				rt904.e.push_back(e70);
				rt904.e.push_back(e1);
				rt904.e.push_back(e3);
				rt904.calc_arity(nullptr);
				sprawformtree ft903 = std::make_shared<raw_form_tree>(elem::NONE, rt904);
				sprawformtree ft902 = std::make_shared<raw_form_tree>(elem::NOT, ft903);
				sprawformtree ft890 = std::make_shared<raw_form_tree>(elem::AND, ft891, ft902);
				raw_rule rr905;
				rr905.h.push_back(rt887);
				rr905.h.push_back(rt888);
				rr905.h.push_back(rt889);
				rr905.set_prft(ft890);
				raw_term rt906;
				rt906.neg = false;
				rt906.extype = raw_term::REL;
				rt906.e.push_back(e46);
				rt906.e.push_back(e1);
				rt906.e.push_back(e2);
				rt906.e.push_back(e3);
				rt906.calc_arity(nullptr);
				raw_term rt914;
				rt914.neg = false;
				rt914.extype = raw_term::REL;
				rt914.e.push_back(e6);
				rt914.e.push_back(e1);
				rt914.e.push_back(e37);
				rt914.e.push_back(e2);
				rt914.e.push_back(e867);
				rt914.e.push_back(e868);
				rt914.e.push_back(e3);
				rt914.calc_arity(nullptr);
				sprawformtree ft913 = std::make_shared<raw_form_tree>(elem::NONE, rt914);
				raw_term rt916;
				rt916.neg = false;
				rt916.extype = raw_term::REL;
				rt916.e.push_back(e6);
				rt916.e.push_back(e1);
				rt916.e.push_back(e7);
				rt916.e.push_back(e867);
				rt916.e.push_back(e871);
				rt916.e.push_back(e205);
				rt916.e.push_back(e3);
				rt916.calc_arity(nullptr);
				sprawformtree ft915 = std::make_shared<raw_form_tree>(elem::NONE, rt916);
				sprawformtree ft912 = std::make_shared<raw_form_tree>(elem::AND, ft913, ft915);
				raw_term rt918;
				rt918.neg = false;
				rt918.extype = raw_term::REL;
				rt918.e.push_back(e879);
				rt918.e.push_back(e1);
				rt918.e.push_back(e868);
				rt918.e.push_back(e236);
				rt918.e.push_back(e251);
				rt918.e.push_back(e3);
				rt918.calc_arity(nullptr);
				sprawformtree ft917 = std::make_shared<raw_form_tree>(elem::NONE, rt918);
				sprawformtree ft911 = std::make_shared<raw_form_tree>(elem::AND, ft912, ft917);
				elem e920;
				e920.type = elem::VAR;
				e920.e = d.get_lexeme("?ds1");
				raw_term rt921;
				rt921.neg = false;
				rt921.extype = raw_term::REL;
				rt921.e.push_back(e468);
				rt921.e.push_back(e1);
				rt921.e.push_back(e236);
				rt921.e.push_back(e251);
				rt921.e.push_back(e205);
				rt921.e.push_back(e920);
				rt921.e.push_back(e3);
				rt921.calc_arity(nullptr);
				sprawformtree ft919 = std::make_shared<raw_form_tree>(elem::NONE, rt921);
				sprawformtree ft910 = std::make_shared<raw_form_tree>(elem::AND, ft911, ft919);
				elem e923;
				e923.type = elem::VAR;
				e923.e = d.get_lexeme("?ds2");
				raw_term rt924;
				rt924.neg = false;
				rt924.extype = raw_term::REL;
				rt924.e.push_back(e798);
				rt924.e.push_back(e1);
				rt924.e.push_back(e205);
				rt924.e.push_back(e923);
				rt924.e.push_back(e3);
				rt924.calc_arity(nullptr);
				sprawformtree ft922 = std::make_shared<raw_form_tree>(elem::NONE, rt924);
				sprawformtree ft909 = std::make_shared<raw_form_tree>(elem::AND, ft910, ft922);
				raw_term rt927;
				rt927.neg = false;
				rt927.extype = raw_term::REL;
				rt927.e.push_back(e668);
				rt927.e.push_back(e1);
				rt927.e.push_back(e236);
				rt927.e.push_back(e251);
				rt927.e.push_back(e3);
				rt927.calc_arity(nullptr);
				sprawformtree ft926 = std::make_shared<raw_form_tree>(elem::NONE, rt927);
				raw_term rt929;
				rt929.neg = false;
				rt929.extype = raw_term::REL;
				rt929.e.push_back(e676);
				rt929.e.push_back(e1);
				rt929.e.push_back(e236);
				rt929.e.push_back(e251);
				rt929.e.push_back(e3);
				rt929.calc_arity(nullptr);
				sprawformtree ft928 = std::make_shared<raw_form_tree>(elem::NONE, rt929);
				sprawformtree ft925 = std::make_shared<raw_form_tree>(elem::ALT, ft926, ft928);
				sprawformtree ft908 = std::make_shared<raw_form_tree>(elem::AND, ft909, ft925);
				raw_term rt931;
				rt931.neg = false;
				rt931.extype = raw_term::REL;
				rt931.e.push_back(e42);
				rt931.e.push_back(e1);
				rt931.e.push_back(e3);
				rt931.calc_arity(nullptr);
				sprawformtree ft930 = std::make_shared<raw_form_tree>(elem::NONE, rt931);
				sprawformtree ft907 = std::make_shared<raw_form_tree>(elem::AND, ft908, ft930);
				raw_rule rr932;
				rr932.h.push_back(rt906);
				rr932.set_prft(ft907);
				elem &e933 = out_rel;
				elem e934;
				e934.type = elem::VAR;
				e934.e = d.get_lexeme("?ds");
				raw_term rt935;
				rt935.neg = false;
				rt935.extype = raw_term::REL;
				rt935.e.push_back(e933);
				rt935.e.push_back(e1);
				rt935.e.push_back(e871);
				rt935.e.push_back(e934);
				rt935.e.push_back(e3);
				rt935.calc_arity(nullptr);
				raw_term rt943;
				rt943.neg = false;
				rt943.extype = raw_term::REL;
				rt943.e.push_back(e6);
				rt943.e.push_back(e1);
				rt943.e.push_back(e37);
				rt943.e.push_back(e2);
				rt943.e.push_back(e867);
				rt943.e.push_back(e868);
				rt943.e.push_back(e3);
				rt943.calc_arity(nullptr);
				sprawformtree ft942 = std::make_shared<raw_form_tree>(elem::NONE, rt943);
				raw_term rt945;
				rt945.neg = false;
				rt945.extype = raw_term::REL;
				rt945.e.push_back(e6);
				rt945.e.push_back(e1);
				rt945.e.push_back(e7);
				rt945.e.push_back(e867);
				rt945.e.push_back(e871);
				rt945.e.push_back(e205);
				rt945.e.push_back(e3);
				rt945.calc_arity(nullptr);
				sprawformtree ft944 = std::make_shared<raw_form_tree>(elem::NONE, rt945);
				sprawformtree ft941 = std::make_shared<raw_form_tree>(elem::AND, ft942, ft944);
				raw_term rt947;
				rt947.neg = false;
				rt947.extype = raw_term::REL;
				rt947.e.push_back(e879);
				rt947.e.push_back(e1);
				rt947.e.push_back(e868);
				rt947.e.push_back(e236);
				rt947.e.push_back(e251);
				rt947.e.push_back(e3);
				rt947.calc_arity(nullptr);
				sprawformtree ft946 = std::make_shared<raw_form_tree>(elem::NONE, rt947);
				sprawformtree ft940 = std::make_shared<raw_form_tree>(elem::AND, ft941, ft946);
				raw_term rt949;
				rt949.neg = false;
				rt949.extype = raw_term::REL;
				rt949.e.push_back(e798);
				rt949.e.push_back(e1);
				rt949.e.push_back(e205);
				rt949.e.push_back(e934);
				rt949.e.push_back(e3);
				rt949.calc_arity(nullptr);
				sprawformtree ft948 = std::make_shared<raw_form_tree>(elem::NONE, rt949);
				sprawformtree ft939 = std::make_shared<raw_form_tree>(elem::AND, ft940, ft948);
				raw_term rt951;
				rt951.neg = false;
				rt951.extype = raw_term::REL;
				rt951.e.push_back(e468);
				rt951.e.push_back(e1);
				rt951.e.push_back(e236);
				rt951.e.push_back(e251);
				rt951.e.push_back(e205);
				rt951.e.push_back(e934);
				rt951.e.push_back(e3);
				rt951.calc_arity(nullptr);
				sprawformtree ft950 = std::make_shared<raw_form_tree>(elem::NONE, rt951);
				sprawformtree ft938 = std::make_shared<raw_form_tree>(elem::AND, ft939, ft950);
				raw_term rt953;
				rt953.neg = false;
				rt953.extype = raw_term::REL;
				rt953.e.push_back(e668);
				rt953.e.push_back(e1);
				rt953.e.push_back(e236);
				rt953.e.push_back(e251);
				rt953.e.push_back(e3);
				rt953.calc_arity(nullptr);
				sprawformtree ft952 = std::make_shared<raw_form_tree>(elem::NONE, rt953);
				sprawformtree ft937 = std::make_shared<raw_form_tree>(elem::AND, ft938, ft952);
				raw_term rt955;
				rt955.neg = false;
				rt955.extype = raw_term::REL;
				rt955.e.push_back(e42);
				rt955.e.push_back(e1);
				rt955.e.push_back(e3);
				rt955.calc_arity(nullptr);
				sprawformtree ft954 = std::make_shared<raw_form_tree>(elem::NONE, rt955);
				sprawformtree ft936 = std::make_shared<raw_form_tree>(elem::AND, ft937, ft954);
				raw_rule rr956;
				rr956.h.push_back(rt935);
				rr956.set_prft(ft936);
				raw_term rt957;
				rt957.neg = false;
				rt957.extype = raw_term::REL;
				rt957.e.push_back(e790);
				rt957.e.push_back(e1);
				rt957.e.push_back(e236);
				rt957.e.push_back(e3);
				rt957.calc_arity(nullptr);
				elem e961;
				e961.type = elem::VAR;
				e961.e = d.get_lexeme("?n");
				raw_term rt962;
				rt962.neg = false;
				rt962.extype = raw_term::REL;
				rt962.e.push_back(e6);
				rt962.e.push_back(e1);
				rt962.e.push_back(e7);
				rt962.e.push_back(e2);
				rt962.e.push_back(e961);
				rt962.e.push_back(e236);
				rt962.e.push_back(e3);
				rt962.calc_arity(nullptr);
				sprawformtree ft960 = std::make_shared<raw_form_tree>(elem::NONE, rt962);
				raw_term rt964;
				rt964.neg = false;
				rt964.extype = raw_term::REL;
				rt964.e.push_back(e44);
				rt964.e.push_back(e1);
				rt964.e.push_back(e3);
				rt964.calc_arity(nullptr);
				sprawformtree ft963 = std::make_shared<raw_form_tree>(elem::NONE, rt964);
				sprawformtree ft959 = std::make_shared<raw_form_tree>(elem::AND, ft960, ft963);
				raw_term rt967;
				rt967.neg = false;
				rt967.extype = raw_term::REL;
				rt967.e.push_back(e52);
				rt967.e.push_back(e1);
				rt967.e.push_back(e3);
				rt967.calc_arity(nullptr);
				sprawformtree ft966 = std::make_shared<raw_form_tree>(elem::NONE, rt967);
				sprawformtree ft965 = std::make_shared<raw_form_tree>(elem::NOT, ft966);
				sprawformtree ft958 = std::make_shared<raw_form_tree>(elem::AND, ft959, ft965);
				raw_rule rr968;
				rr968.h.push_back(rt957);
				rr968.set_prft(ft958);
				raw_term rt969;
				rt969.neg = false;
				rt969.extype = raw_term::REL;
				rt969.e.push_back(e67);
				rt969.e.push_back(e1);
				rt969.e.push_back(e2);
				rt969.e.push_back(e236);
				rt969.e.push_back(e3);
				rt969.calc_arity(nullptr);
				raw_term rt973;
				rt973.neg = false;
				rt973.extype = raw_term::REL;
				rt973.e.push_back(e6);
				rt973.e.push_back(e1);
				rt973.e.push_back(e7);
				rt973.e.push_back(e2);
				rt973.e.push_back(e961);
				rt973.e.push_back(e236);
				rt973.e.push_back(e3);
				rt973.calc_arity(nullptr);
				sprawformtree ft972 = std::make_shared<raw_form_tree>(elem::NONE, rt973);
				raw_term rt975;
				rt975.neg = false;
				rt975.extype = raw_term::REL;
				rt975.e.push_back(e798);
				rt975.e.push_back(e1);
				rt975.e.push_back(e236);
				rt975.e.push_back(e251);
				rt975.e.push_back(e3);
				rt975.calc_arity(nullptr);
				sprawformtree ft974 = std::make_shared<raw_form_tree>(elem::NONE, rt975);
				sprawformtree ft971 = std::make_shared<raw_form_tree>(elem::AND, ft972, ft974);
				raw_term rt977;
				rt977.neg = false;
				rt977.extype = raw_term::REL;
				rt977.e.push_back(e44);
				rt977.e.push_back(e1);
				rt977.e.push_back(e3);
				rt977.calc_arity(nullptr);
				sprawformtree ft976 = std::make_shared<raw_form_tree>(elem::NONE, rt977);
				sprawformtree ft970 = std::make_shared<raw_form_tree>(elem::AND, ft971, ft976);
				raw_rule rr978;
				rr978.h.push_back(rt969);
				rr978.set_prft(ft970);
				raw_term rt979;
				rt979.neg = false;
				rt979.extype = raw_term::REL;
				rt979.e.push_back(e879);
				rt979.e.push_back(e1);
				rt979.e.push_back(e2);
				rt979.e.push_back(e236);
				rt979.e.push_back(e251);
				rt979.e.push_back(e3);
				rt979.calc_arity(nullptr);
				raw_term rt984;
				rt984.neg = false;
				rt984.extype = raw_term::REL;
				rt984.e.push_back(e6);
				rt984.e.push_back(e1);
				rt984.e.push_back(e7);
				rt984.e.push_back(e2);
				rt984.e.push_back(e961);
				rt984.e.push_back(e236);
				rt984.e.push_back(e3);
				rt984.calc_arity(nullptr);
				sprawformtree ft983 = std::make_shared<raw_form_tree>(elem::NONE, rt984);
				raw_term rt986;
				rt986.neg = false;
				rt986.extype = raw_term::REL;
				rt986.e.push_back(e933);
				rt986.e.push_back(e1);
				rt986.e.push_back(e961);
				rt986.e.push_back(e251);
				rt986.e.push_back(e3);
				rt986.calc_arity(nullptr);
				sprawformtree ft985 = std::make_shared<raw_form_tree>(elem::NONE, rt986);
				sprawformtree ft982 = std::make_shared<raw_form_tree>(elem::AND, ft983, ft985);
				raw_term rt988;
				rt988.neg = false;
				rt988.extype = raw_term::REL;
				rt988.e.push_back(e798);
				rt988.e.push_back(e1);
				rt988.e.push_back(e236);
				rt988.e.push_back(e251);
				rt988.e.push_back(e3);
				rt988.calc_arity(nullptr);
				sprawformtree ft987 = std::make_shared<raw_form_tree>(elem::NONE, rt988);
				sprawformtree ft981 = std::make_shared<raw_form_tree>(elem::AND, ft982, ft987);
				raw_term rt990;
				rt990.neg = false;
				rt990.extype = raw_term::REL;
				rt990.e.push_back(e44);
				rt990.e.push_back(e1);
				rt990.e.push_back(e3);
				rt990.calc_arity(nullptr);
				sprawformtree ft989 = std::make_shared<raw_form_tree>(elem::NONE, rt990);
				sprawformtree ft980 = std::make_shared<raw_form_tree>(elem::AND, ft981, ft989);
				raw_rule rr991;
				rr991.h.push_back(rt979);
				rr991.set_prft(ft980);
				raw_term rt992;
				rt992.neg = false;
				rt992.extype = raw_term::REL;
				rt992.e.push_back(e879);
				rt992.e.push_back(e1);
				rt992.e.push_back(e2);
				rt992.e.push_back(e236);
				rt992.e.push_back(e251);
				rt992.e.push_back(e3);
				rt992.calc_arity(nullptr);
				elem e999;
				e999.type = elem::VAR;
				e999.e = d.get_lexeme("?a1");
				elem e1000;
				e1000.type = elem::VAR;
				e1000.e = d.get_lexeme("?a2");
				raw_term rt1001;
				rt1001.neg = false;
				rt1001.extype = raw_term::REL;
				rt1001.e.push_back(e6);
				rt1001.e.push_back(e1);
				rt1001.e.push_back(e12);
				rt1001.e.push_back(e2);
				rt1001.e.push_back(e999);
				rt1001.e.push_back(e1000);
				rt1001.e.push_back(e3);
				rt1001.calc_arity(nullptr);
				sprawformtree ft998 = std::make_shared<raw_form_tree>(elem::NONE, rt1001);
				raw_term rt1003;
				rt1003.neg = false;
				rt1003.extype = raw_term::EQ;
				rt1003.e.push_back(e20);
				rt1003.e.push_back(e109);
				rt1003.e.push_back(e21);
				rt1003.calc_arity(nullptr);
				sprawformtree ft1002 = std::make_shared<raw_form_tree>(elem::NONE, rt1003);
				sprawformtree ft997 = std::make_shared<raw_form_tree>(elem::AND, ft998, ft1002);
				raw_term rt1005;
				rt1005.neg = false;
				rt1005.extype = raw_term::REL;
				rt1005.e.push_back(e157);
				rt1005.e.push_back(e1);
				rt1005.e.push_back(e236);
				rt1005.e.push_back(e999);
				rt1005.e.push_back(e1000);
				rt1005.e.push_back(e3);
				rt1005.calc_arity(nullptr);
				sprawformtree ft1004 = std::make_shared<raw_form_tree>(elem::NONE, rt1005);
				sprawformtree ft996 = std::make_shared<raw_form_tree>(elem::AND, ft997, ft1004);
				raw_term rt1007;
				rt1007.neg = false;
				rt1007.extype = raw_term::REL;
				rt1007.e.push_back(e157);
				rt1007.e.push_back(e1);
				rt1007.e.push_back(e251);
				rt1007.e.push_back(e20);
				rt1007.e.push_back(e21);
				rt1007.e.push_back(e3);
				rt1007.calc_arity(nullptr);
				sprawformtree ft1006 = std::make_shared<raw_form_tree>(elem::NONE, rt1007);
				sprawformtree ft995 = std::make_shared<raw_form_tree>(elem::AND, ft996, ft1006);
				raw_term rt1009;
				rt1009.neg = false;
				rt1009.extype = raw_term::REL;
				rt1009.e.push_back(e798);
				rt1009.e.push_back(e1);
				rt1009.e.push_back(e236);
				rt1009.e.push_back(e251);
				rt1009.e.push_back(e3);
				rt1009.calc_arity(nullptr);
				sprawformtree ft1008 = std::make_shared<raw_form_tree>(elem::NONE, rt1009);
				sprawformtree ft994 = std::make_shared<raw_form_tree>(elem::AND, ft995, ft1008);
				raw_term rt1011;
				rt1011.neg = false;
				rt1011.extype = raw_term::REL;
				rt1011.e.push_back(e44);
				rt1011.e.push_back(e1);
				rt1011.e.push_back(e3);
				rt1011.calc_arity(nullptr);
				sprawformtree ft1010 = std::make_shared<raw_form_tree>(elem::NONE, rt1011);
				sprawformtree ft993 = std::make_shared<raw_form_tree>(elem::AND, ft994, ft1010);
				raw_rule rr1012;
				rr1012.h.push_back(rt992);
				rr1012.set_prft(ft993);
				raw_term rt1013;
				rt1013.neg = false;
				rt1013.extype = raw_term::REL;
				rt1013.e.push_back(e67);
				rt1013.e.push_back(e1);
				rt1013.e.push_back(e2);
				rt1013.e.push_back(e236);
				rt1013.e.push_back(e3);
				rt1013.calc_arity(nullptr);
				raw_term rt1017;
				rt1017.neg = false;
				rt1017.extype = raw_term::REL;
				rt1017.e.push_back(e6);
				rt1017.e.push_back(e1);
				rt1017.e.push_back(e12);
				rt1017.e.push_back(e2);
				rt1017.e.push_back(e999);
				rt1017.e.push_back(e1000);
				rt1017.e.push_back(e3);
				rt1017.calc_arity(nullptr);
				sprawformtree ft1016 = std::make_shared<raw_form_tree>(elem::NONE, rt1017);
				raw_term rt1019;
				rt1019.neg = false;
				rt1019.extype = raw_term::REL;
				rt1019.e.push_back(e157);
				rt1019.e.push_back(e1);
				rt1019.e.push_back(e236);
				rt1019.e.push_back(e999);
				rt1019.e.push_back(e1000);
				rt1019.e.push_back(e3);
				rt1019.calc_arity(nullptr);
				sprawformtree ft1018 = std::make_shared<raw_form_tree>(elem::NONE, rt1019);
				sprawformtree ft1015 = std::make_shared<raw_form_tree>(elem::AND, ft1016, ft1018);
				raw_term rt1021;
				rt1021.neg = false;
				rt1021.extype = raw_term::REL;
				rt1021.e.push_back(e44);
				rt1021.e.push_back(e1);
				rt1021.e.push_back(e3);
				rt1021.calc_arity(nullptr);
				sprawformtree ft1020 = std::make_shared<raw_form_tree>(elem::NONE, rt1021);
				sprawformtree ft1014 = std::make_shared<raw_form_tree>(elem::AND, ft1015, ft1020);
				raw_rule rr1022;
				rr1022.h.push_back(rt1013);
				rr1022.set_prft(ft1014);
				raw_term rt1023;
				rt1023.neg = false;
				rt1023.extype = raw_term::REL;
				rt1023.e.push_back(e879);
				rt1023.e.push_back(e1);
				rt1023.e.push_back(e2);
				rt1023.e.push_back(e236);
				rt1023.e.push_back(e251);
				rt1023.e.push_back(e3);
				rt1023.calc_arity(nullptr);
				raw_term rt1028;
				rt1028.neg = false;
				rt1028.extype = raw_term::REL;
				rt1028.e.push_back(e6);
				rt1028.e.push_back(e1);
				rt1028.e.push_back(e31);
				rt1028.e.push_back(e2);
				rt1028.e.push_back(e3);
				rt1028.calc_arity(nullptr);
				sprawformtree ft1027 = std::make_shared<raw_form_tree>(elem::NONE, rt1028);
				raw_term rt1030;
				rt1030.neg = false;
				rt1030.extype = raw_term::REL;
				rt1030.e.push_back(e153);
				rt1030.e.push_back(e1);
				rt1030.e.push_back(e236);
				rt1030.e.push_back(e3);
				rt1030.calc_arity(nullptr);
				sprawformtree ft1029 = std::make_shared<raw_form_tree>(elem::NONE, rt1030);
				sprawformtree ft1026 = std::make_shared<raw_form_tree>(elem::AND, ft1027, ft1029);
				raw_term rt1032;
				rt1032.neg = false;
				rt1032.extype = raw_term::REL;
				rt1032.e.push_back(e153);
				rt1032.e.push_back(e1);
				rt1032.e.push_back(e251);
				rt1032.e.push_back(e3);
				rt1032.calc_arity(nullptr);
				sprawformtree ft1031 = std::make_shared<raw_form_tree>(elem::NONE, rt1032);
				sprawformtree ft1025 = std::make_shared<raw_form_tree>(elem::AND, ft1026, ft1031);
				raw_term rt1034;
				rt1034.neg = false;
				rt1034.extype = raw_term::REL;
				rt1034.e.push_back(e44);
				rt1034.e.push_back(e1);
				rt1034.e.push_back(e3);
				rt1034.calc_arity(nullptr);
				sprawformtree ft1033 = std::make_shared<raw_form_tree>(elem::NONE, rt1034);
				sprawformtree ft1024 = std::make_shared<raw_form_tree>(elem::AND, ft1025, ft1033);
				raw_rule rr1035;
				rr1035.h.push_back(rt1023);
				rr1035.set_prft(ft1024);
				raw_term rt1036;
				rt1036.neg = false;
				rt1036.extype = raw_term::REL;
				rt1036.e.push_back(e67);
				rt1036.e.push_back(e1);
				rt1036.e.push_back(e2);
				rt1036.e.push_back(e236);
				rt1036.e.push_back(e3);
				rt1036.calc_arity(nullptr);
				raw_term rt1040;
				rt1040.neg = false;
				rt1040.extype = raw_term::REL;
				rt1040.e.push_back(e6);
				rt1040.e.push_back(e1);
				rt1040.e.push_back(e31);
				rt1040.e.push_back(e2);
				rt1040.e.push_back(e3);
				rt1040.calc_arity(nullptr);
				sprawformtree ft1039 = std::make_shared<raw_form_tree>(elem::NONE, rt1040);
				raw_term rt1042;
				rt1042.neg = false;
				rt1042.extype = raw_term::REL;
				rt1042.e.push_back(e153);
				rt1042.e.push_back(e1);
				rt1042.e.push_back(e236);
				rt1042.e.push_back(e3);
				rt1042.calc_arity(nullptr);
				sprawformtree ft1041 = std::make_shared<raw_form_tree>(elem::NONE, rt1042);
				sprawformtree ft1038 = std::make_shared<raw_form_tree>(elem::AND, ft1039, ft1041);
				raw_term rt1044;
				rt1044.neg = false;
				rt1044.extype = raw_term::REL;
				rt1044.e.push_back(e44);
				rt1044.e.push_back(e1);
				rt1044.e.push_back(e3);
				rt1044.calc_arity(nullptr);
				sprawformtree ft1043 = std::make_shared<raw_form_tree>(elem::NONE, rt1044);
				sprawformtree ft1037 = std::make_shared<raw_form_tree>(elem::AND, ft1038, ft1043);
				raw_rule rr1045;
				rr1045.h.push_back(rt1036);
				rr1045.set_prft(ft1037);
				elem e1046;
				e1046.type = elem::VAR;
				e1046.e = d.get_lexeme("?as1");
				elem e1047;
				e1047.type = elem::VAR;
				e1047.e = d.get_lexeme("?as2");
				raw_term rt1048;
				rt1048.neg = false;
				rt1048.extype = raw_term::REL;
				rt1048.e.push_back(e200);
				rt1048.e.push_back(e1);
				rt1048.e.push_back(e1046);
				rt1048.e.push_back(e1047);
				rt1048.e.push_back(e3);
				rt1048.calc_arity(nullptr);
				elem e1049;
				e1049.type = elem::VAR;
				e1049.e = d.get_lexeme("?bs1");
				elem e1050;
				e1050.type = elem::VAR;
				e1050.e = d.get_lexeme("?bs2");
				raw_term rt1051;
				rt1051.neg = false;
				rt1051.extype = raw_term::REL;
				rt1051.e.push_back(e200);
				rt1051.e.push_back(e1);
				rt1051.e.push_back(e1049);
				rt1051.e.push_back(e1050);
				rt1051.e.push_back(e3);
				rt1051.calc_arity(nullptr);
				elem e1055;
				e1055.type = elem::VAR;
				e1055.e = d.get_lexeme("?e2");
				raw_term rt1056;
				rt1056.neg = false;
				rt1056.extype = raw_term::REL;
				rt1056.e.push_back(e6);
				rt1056.e.push_back(e1);
				rt1056.e.push_back(e19);
				rt1056.e.push_back(e2);
				rt1056.e.push_back(e868);
				rt1056.e.push_back(e1055);
				rt1056.e.push_back(e3);
				rt1056.calc_arity(nullptr);
				sprawformtree ft1054 = std::make_shared<raw_form_tree>(elem::NONE, rt1056);
				raw_term rt1059;
				rt1059.neg = false;
				rt1059.extype = raw_term::REL;
				rt1059.e.push_back(e879);
				rt1059.e.push_back(e1);
				rt1059.e.push_back(e868);
				rt1059.e.push_back(e1046);
				rt1059.e.push_back(e1049);
				rt1059.e.push_back(e3);
				rt1059.calc_arity(nullptr);
				sprawformtree ft1058 = std::make_shared<raw_form_tree>(elem::NONE, rt1059);
				raw_term rt1061;
				rt1061.neg = false;
				rt1061.extype = raw_term::REL;
				rt1061.e.push_back(e879);
				rt1061.e.push_back(e1);
				rt1061.e.push_back(e1055);
				rt1061.e.push_back(e1047);
				rt1061.e.push_back(e1050);
				rt1061.e.push_back(e3);
				rt1061.calc_arity(nullptr);
				sprawformtree ft1060 = std::make_shared<raw_form_tree>(elem::NONE, rt1061);
				sprawformtree ft1057 = std::make_shared<raw_form_tree>(elem::AND, ft1058, ft1060);
				sprawformtree ft1053 = std::make_shared<raw_form_tree>(elem::AND, ft1054, ft1057);
				raw_term rt1063;
				rt1063.neg = false;
				rt1063.extype = raw_term::REL;
				rt1063.e.push_back(e44);
				rt1063.e.push_back(e1);
				rt1063.e.push_back(e3);
				rt1063.calc_arity(nullptr);
				sprawformtree ft1062 = std::make_shared<raw_form_tree>(elem::NONE, rt1063);
				sprawformtree ft1052 = std::make_shared<raw_form_tree>(elem::AND, ft1053, ft1062);
				raw_rule rr1064;
				rr1064.h.push_back(rt1048);
				rr1064.h.push_back(rt1051);
				rr1064.set_prft(ft1052);
				raw_term rt1065;
				rt1065.neg = false;
				rt1065.extype = raw_term::REL;
				rt1065.e.push_back(e879);
				rt1065.e.push_back(e1);
				rt1065.e.push_back(e2);
				rt1065.e.push_back(e236);
				rt1065.e.push_back(e251);
				rt1065.e.push_back(e3);
				rt1065.calc_arity(nullptr);
				raw_term rt1071;
				rt1071.neg = false;
				rt1071.extype = raw_term::REL;
				rt1071.e.push_back(e6);
				rt1071.e.push_back(e1);
				rt1071.e.push_back(e19);
				rt1071.e.push_back(e2);
				rt1071.e.push_back(e868);
				rt1071.e.push_back(e1055);
				rt1071.e.push_back(e3);
				rt1071.calc_arity(nullptr);
				sprawformtree ft1070 = std::make_shared<raw_form_tree>(elem::NONE, rt1071);
				raw_term rt1074;
				rt1074.neg = false;
				rt1074.extype = raw_term::REL;
				rt1074.e.push_back(e879);
				rt1074.e.push_back(e1);
				rt1074.e.push_back(e868);
				rt1074.e.push_back(e1046);
				rt1074.e.push_back(e1049);
				rt1074.e.push_back(e3);
				rt1074.calc_arity(nullptr);
				sprawformtree ft1073 = std::make_shared<raw_form_tree>(elem::NONE, rt1074);
				raw_term rt1076;
				rt1076.neg = false;
				rt1076.extype = raw_term::REL;
				rt1076.e.push_back(e879);
				rt1076.e.push_back(e1);
				rt1076.e.push_back(e1055);
				rt1076.e.push_back(e1047);
				rt1076.e.push_back(e1050);
				rt1076.e.push_back(e3);
				rt1076.calc_arity(nullptr);
				sprawformtree ft1075 = std::make_shared<raw_form_tree>(elem::NONE, rt1076);
				sprawformtree ft1072 = std::make_shared<raw_form_tree>(elem::AND, ft1073, ft1075);
				sprawformtree ft1069 = std::make_shared<raw_form_tree>(elem::AND, ft1070, ft1072);
				raw_term rt1078;
				rt1078.neg = false;
				rt1078.extype = raw_term::REL;
				rt1078.e.push_back(e207);
				rt1078.e.push_back(e1);
				rt1078.e.push_back(e236);
				rt1078.e.push_back(e1046);
				rt1078.e.push_back(e1047);
				rt1078.e.push_back(e3);
				rt1078.calc_arity(nullptr);
				sprawformtree ft1077 = std::make_shared<raw_form_tree>(elem::NONE, rt1078);
				sprawformtree ft1068 = std::make_shared<raw_form_tree>(elem::AND, ft1069, ft1077);
				raw_term rt1080;
				rt1080.neg = false;
				rt1080.extype = raw_term::REL;
				rt1080.e.push_back(e207);
				rt1080.e.push_back(e1);
				rt1080.e.push_back(e251);
				rt1080.e.push_back(e1049);
				rt1080.e.push_back(e1050);
				rt1080.e.push_back(e3);
				rt1080.calc_arity(nullptr);
				sprawformtree ft1079 = std::make_shared<raw_form_tree>(elem::NONE, rt1080);
				sprawformtree ft1067 = std::make_shared<raw_form_tree>(elem::AND, ft1068, ft1079);
				raw_term rt1082;
				rt1082.neg = false;
				rt1082.extype = raw_term::REL;
				rt1082.e.push_back(e44);
				rt1082.e.push_back(e1);
				rt1082.e.push_back(e3);
				rt1082.calc_arity(nullptr);
				sprawformtree ft1081 = std::make_shared<raw_form_tree>(elem::NONE, rt1082);
				sprawformtree ft1066 = std::make_shared<raw_form_tree>(elem::AND, ft1067, ft1081);
				raw_rule rr1083;
				rr1083.h.push_back(rt1065);
				rr1083.set_prft(ft1066);
				raw_term rt1084;
				rt1084.neg = false;
				rt1084.extype = raw_term::REL;
				rt1084.e.push_back(e200);
				rt1084.e.push_back(e1);
				rt1084.e.push_back(e1046);
				rt1084.e.push_back(e1047);
				rt1084.e.push_back(e3);
				rt1084.calc_arity(nullptr);
				raw_term rt1089;
				rt1089.neg = false;
				rt1089.extype = raw_term::REL;
				rt1089.e.push_back(e6);
				rt1089.e.push_back(e1);
				rt1089.e.push_back(e19);
				rt1089.e.push_back(e2);
				rt1089.e.push_back(e868);
				rt1089.e.push_back(e1055);
				rt1089.e.push_back(e3);
				rt1089.calc_arity(nullptr);
				sprawformtree ft1088 = std::make_shared<raw_form_tree>(elem::NONE, rt1089);
				raw_term rt1091;
				rt1091.neg = false;
				rt1091.extype = raw_term::REL;
				rt1091.e.push_back(e67);
				rt1091.e.push_back(e1);
				rt1091.e.push_back(e868);
				rt1091.e.push_back(e1046);
				rt1091.e.push_back(e3);
				rt1091.calc_arity(nullptr);
				sprawformtree ft1090 = std::make_shared<raw_form_tree>(elem::NONE, rt1091);
				sprawformtree ft1087 = std::make_shared<raw_form_tree>(elem::AND, ft1088, ft1090);
				raw_term rt1093;
				rt1093.neg = false;
				rt1093.extype = raw_term::REL;
				rt1093.e.push_back(e67);
				rt1093.e.push_back(e1);
				rt1093.e.push_back(e1055);
				rt1093.e.push_back(e1047);
				rt1093.e.push_back(e3);
				rt1093.calc_arity(nullptr);
				sprawformtree ft1092 = std::make_shared<raw_form_tree>(elem::NONE, rt1093);
				sprawformtree ft1086 = std::make_shared<raw_form_tree>(elem::AND, ft1087, ft1092);
				raw_term rt1095;
				rt1095.neg = false;
				rt1095.extype = raw_term::REL;
				rt1095.e.push_back(e44);
				rt1095.e.push_back(e1);
				rt1095.e.push_back(e3);
				rt1095.calc_arity(nullptr);
				sprawformtree ft1094 = std::make_shared<raw_form_tree>(elem::NONE, rt1095);
				sprawformtree ft1085 = std::make_shared<raw_form_tree>(elem::AND, ft1086, ft1094);
				raw_rule rr1096;
				rr1096.h.push_back(rt1084);
				rr1096.set_prft(ft1085);
				raw_term rt1097;
				rt1097.neg = false;
				rt1097.extype = raw_term::REL;
				rt1097.e.push_back(e67);
				rt1097.e.push_back(e1);
				rt1097.e.push_back(e2);
				rt1097.e.push_back(e236);
				rt1097.e.push_back(e3);
				rt1097.calc_arity(nullptr);
				raw_term rt1103;
				rt1103.neg = false;
				rt1103.extype = raw_term::REL;
				rt1103.e.push_back(e6);
				rt1103.e.push_back(e1);
				rt1103.e.push_back(e19);
				rt1103.e.push_back(e2);
				rt1103.e.push_back(e868);
				rt1103.e.push_back(e1055);
				rt1103.e.push_back(e3);
				rt1103.calc_arity(nullptr);
				sprawformtree ft1102 = std::make_shared<raw_form_tree>(elem::NONE, rt1103);
				raw_term rt1105;
				rt1105.neg = false;
				rt1105.extype = raw_term::REL;
				rt1105.e.push_back(e67);
				rt1105.e.push_back(e1);
				rt1105.e.push_back(e868);
				rt1105.e.push_back(e1046);
				rt1105.e.push_back(e3);
				rt1105.calc_arity(nullptr);
				sprawformtree ft1104 = std::make_shared<raw_form_tree>(elem::NONE, rt1105);
				sprawformtree ft1101 = std::make_shared<raw_form_tree>(elem::AND, ft1102, ft1104);
				raw_term rt1107;
				rt1107.neg = false;
				rt1107.extype = raw_term::REL;
				rt1107.e.push_back(e67);
				rt1107.e.push_back(e1);
				rt1107.e.push_back(e1055);
				rt1107.e.push_back(e1047);
				rt1107.e.push_back(e3);
				rt1107.calc_arity(nullptr);
				sprawformtree ft1106 = std::make_shared<raw_form_tree>(elem::NONE, rt1107);
				sprawformtree ft1100 = std::make_shared<raw_form_tree>(elem::AND, ft1101, ft1106);
				raw_term rt1109;
				rt1109.neg = false;
				rt1109.extype = raw_term::REL;
				rt1109.e.push_back(e207);
				rt1109.e.push_back(e1);
				rt1109.e.push_back(e236);
				rt1109.e.push_back(e1046);
				rt1109.e.push_back(e1047);
				rt1109.e.push_back(e3);
				rt1109.calc_arity(nullptr);
				sprawformtree ft1108 = std::make_shared<raw_form_tree>(elem::NONE, rt1109);
				sprawformtree ft1099 = std::make_shared<raw_form_tree>(elem::AND, ft1100, ft1108);
				raw_term rt1111;
				rt1111.neg = false;
				rt1111.extype = raw_term::REL;
				rt1111.e.push_back(e44);
				rt1111.e.push_back(e1);
				rt1111.e.push_back(e3);
				rt1111.calc_arity(nullptr);
				sprawformtree ft1110 = std::make_shared<raw_form_tree>(elem::NONE, rt1111);
				sprawformtree ft1098 = std::make_shared<raw_form_tree>(elem::AND, ft1099, ft1110);
				raw_rule rr1112;
				rr1112.h.push_back(rt1097);
				rr1112.set_prft(ft1098);
				raw_term rt1113;
				rt1113.neg = false;
				rt1113.extype = raw_term::REL;
				rt1113.e.push_back(e200);
				rt1113.e.push_back(e1);
				rt1113.e.push_back(e1046);
				rt1113.e.push_back(e1047);
				rt1113.e.push_back(e3);
				rt1113.calc_arity(nullptr);
				raw_term rt1114;
				rt1114.neg = false;
				rt1114.extype = raw_term::REL;
				rt1114.e.push_back(e200);
				rt1114.e.push_back(e1);
				rt1114.e.push_back(e1049);
				rt1114.e.push_back(e1050);
				rt1114.e.push_back(e3);
				rt1114.calc_arity(nullptr);
				raw_term rt1118;
				rt1118.neg = false;
				rt1118.extype = raw_term::REL;
				rt1118.e.push_back(e6);
				rt1118.e.push_back(e1);
				rt1118.e.push_back(e26);
				rt1118.e.push_back(e2);
				rt1118.e.push_back(e868);
				rt1118.e.push_back(e1055);
				rt1118.e.push_back(e3);
				rt1118.calc_arity(nullptr);
				sprawformtree ft1117 = std::make_shared<raw_form_tree>(elem::NONE, rt1118);
				raw_term rt1121;
				rt1121.neg = false;
				rt1121.extype = raw_term::REL;
				rt1121.e.push_back(e879);
				rt1121.e.push_back(e1);
				rt1121.e.push_back(e868);
				rt1121.e.push_back(e1046);
				rt1121.e.push_back(e1049);
				rt1121.e.push_back(e3);
				rt1121.calc_arity(nullptr);
				sprawformtree ft1120 = std::make_shared<raw_form_tree>(elem::NONE, rt1121);
				raw_term rt1123;
				rt1123.neg = false;
				rt1123.extype = raw_term::REL;
				rt1123.e.push_back(e879);
				rt1123.e.push_back(e1);
				rt1123.e.push_back(e1055);
				rt1123.e.push_back(e1047);
				rt1123.e.push_back(e1050);
				rt1123.e.push_back(e3);
				rt1123.calc_arity(nullptr);
				sprawformtree ft1122 = std::make_shared<raw_form_tree>(elem::NONE, rt1123);
				sprawformtree ft1119 = std::make_shared<raw_form_tree>(elem::AND, ft1120, ft1122);
				sprawformtree ft1116 = std::make_shared<raw_form_tree>(elem::AND, ft1117, ft1119);
				raw_term rt1125;
				rt1125.neg = false;
				rt1125.extype = raw_term::REL;
				rt1125.e.push_back(e44);
				rt1125.e.push_back(e1);
				rt1125.e.push_back(e3);
				rt1125.calc_arity(nullptr);
				sprawformtree ft1124 = std::make_shared<raw_form_tree>(elem::NONE, rt1125);
				sprawformtree ft1115 = std::make_shared<raw_form_tree>(elem::AND, ft1116, ft1124);
				raw_rule rr1126;
				rr1126.h.push_back(rt1113);
				rr1126.h.push_back(rt1114);
				rr1126.set_prft(ft1115);
				raw_term rt1127;
				rt1127.neg = false;
				rt1127.extype = raw_term::REL;
				rt1127.e.push_back(e879);
				rt1127.e.push_back(e1);
				rt1127.e.push_back(e2);
				rt1127.e.push_back(e236);
				rt1127.e.push_back(e251);
				rt1127.e.push_back(e3);
				rt1127.calc_arity(nullptr);
				raw_term rt1133;
				rt1133.neg = false;
				rt1133.extype = raw_term::REL;
				rt1133.e.push_back(e6);
				rt1133.e.push_back(e1);
				rt1133.e.push_back(e26);
				rt1133.e.push_back(e2);
				rt1133.e.push_back(e868);
				rt1133.e.push_back(e1055);
				rt1133.e.push_back(e3);
				rt1133.calc_arity(nullptr);
				sprawformtree ft1132 = std::make_shared<raw_form_tree>(elem::NONE, rt1133);
				raw_term rt1136;
				rt1136.neg = false;
				rt1136.extype = raw_term::REL;
				rt1136.e.push_back(e879);
				rt1136.e.push_back(e1);
				rt1136.e.push_back(e868);
				rt1136.e.push_back(e1046);
				rt1136.e.push_back(e1049);
				rt1136.e.push_back(e3);
				rt1136.calc_arity(nullptr);
				sprawformtree ft1135 = std::make_shared<raw_form_tree>(elem::NONE, rt1136);
				raw_term rt1138;
				rt1138.neg = false;
				rt1138.extype = raw_term::REL;
				rt1138.e.push_back(e879);
				rt1138.e.push_back(e1);
				rt1138.e.push_back(e1055);
				rt1138.e.push_back(e1047);
				rt1138.e.push_back(e1050);
				rt1138.e.push_back(e3);
				rt1138.calc_arity(nullptr);
				sprawformtree ft1137 = std::make_shared<raw_form_tree>(elem::NONE, rt1138);
				sprawformtree ft1134 = std::make_shared<raw_form_tree>(elem::ALT, ft1135, ft1137);
				sprawformtree ft1131 = std::make_shared<raw_form_tree>(elem::AND, ft1132, ft1134);
				raw_term rt1140;
				rt1140.neg = false;
				rt1140.extype = raw_term::REL;
				rt1140.e.push_back(e207);
				rt1140.e.push_back(e1);
				rt1140.e.push_back(e236);
				rt1140.e.push_back(e1046);
				rt1140.e.push_back(e1047);
				rt1140.e.push_back(e3);
				rt1140.calc_arity(nullptr);
				sprawformtree ft1139 = std::make_shared<raw_form_tree>(elem::NONE, rt1140);
				sprawformtree ft1130 = std::make_shared<raw_form_tree>(elem::AND, ft1131, ft1139);
				raw_term rt1142;
				rt1142.neg = false;
				rt1142.extype = raw_term::REL;
				rt1142.e.push_back(e207);
				rt1142.e.push_back(e1);
				rt1142.e.push_back(e251);
				rt1142.e.push_back(e1049);
				rt1142.e.push_back(e1050);
				rt1142.e.push_back(e3);
				rt1142.calc_arity(nullptr);
				sprawformtree ft1141 = std::make_shared<raw_form_tree>(elem::NONE, rt1142);
				sprawformtree ft1129 = std::make_shared<raw_form_tree>(elem::AND, ft1130, ft1141);
				raw_term rt1144;
				rt1144.neg = false;
				rt1144.extype = raw_term::REL;
				rt1144.e.push_back(e44);
				rt1144.e.push_back(e1);
				rt1144.e.push_back(e3);
				rt1144.calc_arity(nullptr);
				sprawformtree ft1143 = std::make_shared<raw_form_tree>(elem::NONE, rt1144);
				sprawformtree ft1128 = std::make_shared<raw_form_tree>(elem::AND, ft1129, ft1143);
				raw_rule rr1145;
				rr1145.h.push_back(rt1127);
				rr1145.set_prft(ft1128);
				raw_term rt1146;
				rt1146.neg = false;
				rt1146.extype = raw_term::REL;
				rt1146.e.push_back(e200);
				rt1146.e.push_back(e1);
				rt1146.e.push_back(e1046);
				rt1146.e.push_back(e1047);
				rt1146.e.push_back(e3);
				rt1146.calc_arity(nullptr);
				raw_term rt1151;
				rt1151.neg = false;
				rt1151.extype = raw_term::REL;
				rt1151.e.push_back(e6);
				rt1151.e.push_back(e1);
				rt1151.e.push_back(e26);
				rt1151.e.push_back(e2);
				rt1151.e.push_back(e868);
				rt1151.e.push_back(e1055);
				rt1151.e.push_back(e3);
				rt1151.calc_arity(nullptr);
				sprawformtree ft1150 = std::make_shared<raw_form_tree>(elem::NONE, rt1151);
				raw_term rt1153;
				rt1153.neg = false;
				rt1153.extype = raw_term::REL;
				rt1153.e.push_back(e67);
				rt1153.e.push_back(e1);
				rt1153.e.push_back(e868);
				rt1153.e.push_back(e1046);
				rt1153.e.push_back(e3);
				rt1153.calc_arity(nullptr);
				sprawformtree ft1152 = std::make_shared<raw_form_tree>(elem::NONE, rt1153);
				sprawformtree ft1149 = std::make_shared<raw_form_tree>(elem::AND, ft1150, ft1152);
				raw_term rt1155;
				rt1155.neg = false;
				rt1155.extype = raw_term::REL;
				rt1155.e.push_back(e67);
				rt1155.e.push_back(e1);
				rt1155.e.push_back(e1055);
				rt1155.e.push_back(e1047);
				rt1155.e.push_back(e3);
				rt1155.calc_arity(nullptr);
				sprawformtree ft1154 = std::make_shared<raw_form_tree>(elem::NONE, rt1155);
				sprawformtree ft1148 = std::make_shared<raw_form_tree>(elem::AND, ft1149, ft1154);
				raw_term rt1157;
				rt1157.neg = false;
				rt1157.extype = raw_term::REL;
				rt1157.e.push_back(e44);
				rt1157.e.push_back(e1);
				rt1157.e.push_back(e3);
				rt1157.calc_arity(nullptr);
				sprawformtree ft1156 = std::make_shared<raw_form_tree>(elem::NONE, rt1157);
				sprawformtree ft1147 = std::make_shared<raw_form_tree>(elem::AND, ft1148, ft1156);
				raw_rule rr1158;
				rr1158.h.push_back(rt1146);
				rr1158.set_prft(ft1147);
				raw_term rt1159;
				rt1159.neg = false;
				rt1159.extype = raw_term::REL;
				rt1159.e.push_back(e67);
				rt1159.e.push_back(e1);
				rt1159.e.push_back(e2);
				rt1159.e.push_back(e236);
				rt1159.e.push_back(e3);
				rt1159.calc_arity(nullptr);
				raw_term rt1165;
				rt1165.neg = false;
				rt1165.extype = raw_term::REL;
				rt1165.e.push_back(e6);
				rt1165.e.push_back(e1);
				rt1165.e.push_back(e26);
				rt1165.e.push_back(e2);
				rt1165.e.push_back(e868);
				rt1165.e.push_back(e1055);
				rt1165.e.push_back(e3);
				rt1165.calc_arity(nullptr);
				sprawformtree ft1164 = std::make_shared<raw_form_tree>(elem::NONE, rt1165);
				raw_term rt1167;
				rt1167.neg = false;
				rt1167.extype = raw_term::REL;
				rt1167.e.push_back(e67);
				rt1167.e.push_back(e1);
				rt1167.e.push_back(e868);
				rt1167.e.push_back(e1046);
				rt1167.e.push_back(e3);
				rt1167.calc_arity(nullptr);
				sprawformtree ft1166 = std::make_shared<raw_form_tree>(elem::NONE, rt1167);
				sprawformtree ft1163 = std::make_shared<raw_form_tree>(elem::AND, ft1164, ft1166);
				raw_term rt1169;
				rt1169.neg = false;
				rt1169.extype = raw_term::REL;
				rt1169.e.push_back(e67);
				rt1169.e.push_back(e1);
				rt1169.e.push_back(e1055);
				rt1169.e.push_back(e1047);
				rt1169.e.push_back(e3);
				rt1169.calc_arity(nullptr);
				sprawformtree ft1168 = std::make_shared<raw_form_tree>(elem::NONE, rt1169);
				sprawformtree ft1162 = std::make_shared<raw_form_tree>(elem::AND, ft1163, ft1168);
				raw_term rt1171;
				rt1171.neg = false;
				rt1171.extype = raw_term::REL;
				rt1171.e.push_back(e207);
				rt1171.e.push_back(e1);
				rt1171.e.push_back(e236);
				rt1171.e.push_back(e1046);
				rt1171.e.push_back(e1047);
				rt1171.e.push_back(e3);
				rt1171.calc_arity(nullptr);
				sprawformtree ft1170 = std::make_shared<raw_form_tree>(elem::NONE, rt1171);
				sprawformtree ft1161 = std::make_shared<raw_form_tree>(elem::AND, ft1162, ft1170);
				raw_term rt1173;
				rt1173.neg = false;
				rt1173.extype = raw_term::REL;
				rt1173.e.push_back(e44);
				rt1173.e.push_back(e1);
				rt1173.e.push_back(e3);
				rt1173.calc_arity(nullptr);
				sprawformtree ft1172 = std::make_shared<raw_form_tree>(elem::NONE, rt1173);
				sprawformtree ft1160 = std::make_shared<raw_form_tree>(elem::AND, ft1161, ft1172);
				raw_rule rr1174;
				rr1174.h.push_back(rt1159);
				rr1174.set_prft(ft1160);
				raw_prog &rp1175 = rp;
				rp1175.r.push_back(rr9);
				rp1175.r.push_back(rr16);
				rp1175.r.push_back(rr23);
				rp1175.r.push_back(rr28);
				rp1175.r.push_back(rr33);
				rp1175.r.push_back(rr41);
				rp1175.r.push_back(rr69);
				rp1175.r.push_back(rr74);
				rp1175.r.push_back(rr78);
				rp1175.r.push_back(rr96);
				rp1175.r.push_back(rr100);
				rp1175.r.push_back(rr104);
				rp1175.r.push_back(rr111);
				rp1175.r.push_back(rr116);
				rp1175.r.push_back(rr121);
				rp1175.r.push_back(rr126);
				rp1175.r.push_back(rr131);
				rp1175.r.push_back(rr136);
				rp1175.r.push_back(rr141);
				rp1175.r.push_back(rr149);
				rp1175.r.push_back(rr156);
				rp1175.r.push_back(rr161);
				rp1175.r.push_back(rr170);
				rp1175.r.push_back(rr177);
				rp1175.r.push_back(rr185);
				rp1175.r.push_back(rr193);
				rp1175.r.push_back(rr209);
				rp1175.r.push_back(rr230);
				rp1175.r.push_back(rr245);
				rp1175.r.push_back(rr249);
				rp1175.r.push_back(rr265);
				rp1175.r.push_back(rr285);
				rp1175.r.push_back(rr298);
				rp1175.r.push_back(rr302);
				rp1175.r.push_back(rr319);
				rp1175.r.push_back(rr340);
				rp1175.r.push_back(rr360);
				rp1175.r.push_back(rr385);
				rp1175.r.push_back(rr409);
				rp1175.r.push_back(rr429);
				rp1175.r.push_back(rr452);
				rp1175.r.push_back(rr460);
				rp1175.r.push_back(rr477);
				rp1175.r.push_back(rr495);
				rp1175.r.push_back(rr516);
				rp1175.r.push_back(rr531);
				rp1175.r.push_back(rr547);
				rp1175.r.push_back(rr553);
				rp1175.r.push_back(rr569);
				rp1175.r.push_back(rr587);
				rp1175.r.push_back(rr610);
				rp1175.r.push_back(rr633);
				rp1175.r.push_back(rr651);
				rp1175.r.push_back(rr658);
				rp1175.r.push_back(rr678);
				rp1175.r.push_back(rr702);
				rp1175.r.push_back(rr727);
				rp1175.r.push_back(rr752);
				rp1175.r.push_back(rr774);
				rp1175.r.push_back(rr784);
				rp1175.r.push_back(rr800);
				rp1175.r.push_back(rr833);
				rp1175.r.push_back(rr848);
				rp1175.r.push_back(rr855);
				rp1175.r.push_back(rr860);
				rp1175.r.push_back(rr886);
				rp1175.r.push_back(rr905);
				rp1175.r.push_back(rr932);
				rp1175.r.push_back(rr956);
				rp1175.r.push_back(rr968);
				rp1175.r.push_back(rr978);
				rp1175.r.push_back(rr991);
				rp1175.r.push_back(rr1012);
				rp1175.r.push_back(rr1022);
				rp1175.r.push_back(rr1035);
				rp1175.r.push_back(rr1045);
				rp1175.r.push_back(rr1064);
				rp1175.r.push_back(rr1083);
				rp1175.r.push_back(rr1096);
				rp1175.r.push_back(rr1112);
				rp1175.r.push_back(rr1126);
				rp1175.r.push_back(rr1145);
				rp1175.r.push_back(rr1158);
				rp1175.r.push_back(rr1174);
			}
			
			// Allocate rule name, rule id, head id, body id
			elem rule_name = elem::fresh_var(d), elt_id = elem::fresh_var(d),
				forma_id = elem::fresh_var(d);
		}
	}
}

/* Applies the given transformation on the given program in post-order.
 * I.e. the transformation is applied to the nested programs first and
 * then to the program proper. */

void driver::recursive_transform(raw_prog &rp,
		const std::function<void(raw_prog &)> &f) {
	for(raw_prog &np : rp.nps) {
		recursive_transform(np, f);
	}
	f(rp);
}

/* Checks if the relation the first rule belongs to precedes the
 * relation that the second rule belongs to. A relation precedes another
 * relation if its name precedes the other relation's name. In the case
 * of a tie, a relation precedes another relation if its arity is lower
 * than the other's. */

bool rule_relation_precedes(const raw_rule &rr1, const raw_rule &rr2) {
	if(rr1.h[0].e[0] == rr2.h[0].e[0]) {
		return rr1.h[0].e.size() < rr2.h[0].e.size();
	} else {
		return rr1.h[0].e[0] < rr2.h[0].e[0];
	}
}

/* Convenience function for creating most general rule head for the
 * given relation. */

raw_term driver::relation_to_term(const rel_info &ri) {
	// Get dictionary for generating fresh symbols
	dict_t &d = tbl->get_dict();
	
	std::vector<elem> els = { std::get<0>(ri), elem_openp };
	for(int_t i = 0; i < std::get<1>(ri); i++) {
		els.push_back(elem::fresh_var(d));
	}
	els.push_back(elem_closep);
	return raw_term(els);
}

/* Convenience function to condition the given rule with the given
 * condition term. */

raw_rule condition_rule(raw_rule rr, const raw_term &cond) {
	if(rr.b.empty()) {
		rr.b.push_back({cond});
	} else {
		for(std::vector<raw_term> &bodie : rr.b) {
			bodie.push_back(cond);
		}
	}
	return rr;
}

/* Applies the given transformation to the given program in such a way
 * that it completes in a single step. Does this by separating the given
 * program into an execute and a writeback stage which serves to stop
 * the construction of the next database from interfering with the
 * execution of the current stage. */

void driver::step_transform(raw_prog &rp,
		const std::function<void(raw_prog &)> &f) {
	// Get dictionary for generating fresh symbols
	dict_t &d = tbl->get_dict();
	
	std::map<std::tuple<elem, bool>, elem> freeze_map;
	std::map<elem, std::tuple<elem, bool>> unfreeze_map;
	// Separate the internal rules used to execute the parts of the
	// transformation from the external rules used to expose the results
	// of computation.
	std::set<raw_term> fact_prog;
	std::vector<raw_rule> ext_prog, int_prog;
	// Create a duplicate of each rule in the given program under a
	// generated alias.
	for(raw_rule rr : rp.r) {
		// If the current rule is a fact, store it separately so that we
		// avoid creating unnecessary tmprels
		if(rr.is_b() && rr.b.empty()) {
			fact_prog.insert(rr.h.begin(), rr.h.end());
		} else {
			for(raw_term &rt : rr.h) {
				raw_term rt2 = rt;
				auto it = freeze_map.find(std::make_tuple(rt.e[0], rt.neg));
				if(it != freeze_map.end()) {
					rt.e[0] = it->second;
				} else {
					elem frozen_elem = elem::fresh_temp_sym(d);
					// Store the mapping so that the derived portion of each
					// relation is stored in exactly one place
					unfreeze_map[frozen_elem] = std::make_tuple(rt.e[0], rt.neg);
					rt.e[0] = freeze_map[std::make_tuple(rt.e[0], rt.neg)] = frozen_elem;
				}
				// The internal rule should be positive since the external can be
				// negative.
				rt.neg = false;
				// Update the external interface
				ext_prog.push_back(raw_rule(rt2, rt));
			}
			int_prog.push_back(rr);
		}
	}
	// Apply the modifications from the above loop
	rp.r = int_prog;
	// Execute the transformation on the renamed rules.
	f(rp);
	
	// Partition the rules by relations
	typedef std::set<raw_rule> relation;
	std::map<rel_info, relation> rels;
	for(const raw_rule &rr : rp.r) {
		rels[get_relation_info(rr.h[0])].insert(rr);
	}
	std::map<const relation *, rel_info> rrels;
	for(const auto &[ri, r] : rels) {
		rrels[&r] = ri;
	}
	// Initialize the dependency lists
	std::map<const relation *, std::set<const relation *>> deps, rdeps;
	for(const auto &[k, v] : rels) {
		deps[&v] = {};
		rdeps[&v] = {};
	}
	// Make the adjacency lists based on rule dependency
	for(const auto &[k, v] : rels) {
		for(const raw_rule &rr : v) {
			for(const std::vector<raw_term> &bodie : rr.b) {
				for(const raw_term &rt : bodie) {
					rel_info target = get_relation_info(rt);
					if(rels.find(target) != rels.end()) {
						// Store the edges in both directions so that reverse
						// lookups are easy
						deps[&rels[target]].insert(&v);
						rdeps[&v].insert(&rels[target]);
					}
				}
			}
		}
	}
	// Topologically sort the relations
	std::vector<std::set<const relation *>> sorted;
	// Represents the relations that do not depend on other relations
	std::set<const relation *> current_level;
	for(const auto &[k, v] : rdeps) {
		if(v.empty()) {
			current_level.insert(k);
		}
	}
	// Kahn's algorithm: start from relations with no dependencies and
	// work our way up
	while(!current_level.empty()) {
		std::set<const relation *> next_level;
		for(const relation *n : current_level) {
			for(const relation *m : deps[n]) {
				rdeps[m].erase(n);
				if(rdeps[m].empty()) {
					next_level.insert(m);
				}
			}
			deps[n].clear();
		}
		sorted.push_back(current_level);
		current_level = next_level;
	}
	// If there are interdependencies between rules
	if(sorted.size() > 1) {
		rp.r.clear();
		// At each stage of TML execution, exactly one of the nullary facts
		// in this vector are asserted
		std::vector<elem> clock_states = { elem::fresh_temp_sym(d) };
		// Push the internal rules onto the program using conditioning to
		// control execution order
		for(const std::set<const relation *> v : sorted) {
			// Make a new clock state for the current stage
			const elem clock_state = elem::fresh_temp_sym(d);
			// If the previous state is asserted, then de-assert it and assert
			// this state
			rp.r.push_back(raw_rule({ raw_term(clock_state, std::vector<elem>{}),
				raw_term(clock_states.back(), std::vector<elem>{}).negate() },
				{ raw_term(clock_states.back(), std::vector<elem>{}) }));
			clock_states.push_back(clock_state);
			
			for(const relation *w : v) {
				const raw_term general_head = relation_to_term(rrels[w]);
				rp.r.push_back(raw_rule(general_head.negate(),
					{ general_head, raw_term(clock_states[0], std::vector<elem>{}) }));
				for(raw_rule rr : *w) {
					// Condition everything in the current stage with the same
					// clock state
					rp.r.push_back(condition_rule(rr,
						raw_term(clock_state, std::vector<elem>{})));
				}
			}
		}
		// Start the clock ticking by asserting a state if no other state is
		// asserted
		raw_rule init_clock(raw_term(clock_states[0], std::vector<elem>{}));
		init_clock.b.push_back({});
		for(const elem &e : clock_states) {
			init_clock.b[0].push_back(raw_term(e, std::vector<elem>{}).negate());
		}
		rp.r.push_back(init_clock);
		if(clock_states.size() > 1) {
			// If the previous state is asserted, then de-assert it and assert
			// this state
			rp.r.push_back(raw_rule({ raw_term(clock_states[0], std::vector<elem>{}),
				raw_term(clock_states.back(), std::vector<elem>{}).negate() },
				{ raw_term(clock_states.back(), std::vector<elem>{}) }));
		}
		// Add the external program which serves to writeback the outputs of
		// the internal rules.
		for(raw_rule &rr : ext_prog) {
			// Condition everything in the writeback stage with the same
			// clock state
			rp.r.push_back(condition_rule(rr,
				raw_term(clock_states[0], std::vector<elem>{})));
		}
		// Add the facts section from the original program so that facts are
		// asserted during the writeback stage
		if(fact_prog.size()) {
			rp.r.push_back(condition_rule(
				raw_rule(std::vector<raw_term>(fact_prog.begin(), fact_prog.end()), {}),
				raw_term(clock_states[0], std::vector<elem>{})));
		}
	} else {
		// If there are no interdepencies then we can just restore the
		// original rule names to the transformed program
		for(raw_rule &rr : rp.r) {
			for(raw_term &rt : rr.h) {
				auto jt = unfreeze_map.find(rt.e[0]);
				if(jt != unfreeze_map.end()) {
					auto &[name, neg] = jt->second;
					rt.e[0] = name;
					rt.neg = neg;
				}
			}
		}
		// Add the facts from the original program
		if(fact_prog.size()) {
			rp.r.push_back(raw_rule(std::vector<raw_term>(fact_prog.begin(),
				fact_prog.end()), {}));
		}
	}
}

/* Returns the difference between the two given sets. I.e. the second
 * set removed with multiplicity from the first. */

std::set<elem> set_difference(const std::multiset<elem> &s1,
		const std::set<elem> &s2) {
	std::set<elem> res;
	std::set_difference(s1.begin(), s1.end(), s2.begin(), s2.end(),
		std::inserter(res, res.end()));
	return res;
}

/* Returns the intersection of the two given sets. I.e. all the elems
 * that occur in both sets. */

std::set<elem> set_intersection(const std::set<elem> &s1,
		const std::set<elem> &s2) {
	std::set<elem> res;
	std::set_intersection(s1.begin(), s1.end(), s2.begin(), s2.end(),
		std::inserter(res, res.end()));
	return res;
}

/* Make a term with behavior equivalent to the supplied first order
 * logic formula with the given bound variables. This might involve
 * adding temporary relations to the given program. */

raw_term driver::to_pure_tml(const sprawformtree &t,
		std::vector<raw_rule> &rp, const std::set<elem> &fv) {
	// Get dictionary for generating fresh symbols
	dict_t &d = tbl->get_dict();
	const elem part_id = elem::fresh_temp_sym(d);
	
	switch(t->type) {
		case elem::IMPLIES:
			// Implication is logically equivalent to the following
			return to_pure_tml(std::make_shared<raw_form_tree>(elem::ALT,
				std::make_shared<raw_form_tree>(elem::NOT, t->l), t->r), rp, fv);
		case elem::COIMPLIES:
			// Co-implication is logically equivalent to the following
			return to_pure_tml(std::make_shared<raw_form_tree>(elem::AND,
				std::make_shared<raw_form_tree>(elem::IMPLIES, t->l, t->r),
				std::make_shared<raw_form_tree>(elem::IMPLIES, t->r, t->l)), rp, fv);
		case elem::AND: {
			// Collect all the conjuncts within the tree top
			std::vector<sprawformtree> ands;
			flatten_associative(elem::AND, t, ands);
			// Collect the free variables in each conjunct. The intersection
			// of variables between one and the rest is what will need to be
			// exported
			std::multiset<elem> all_vars(fv.begin(), fv.end());
			std::map<const sprawformtree, std::set<elem>> fvs;
			for(const sprawformtree &tree : ands) {
				fvs[tree] = collect_free_vars(tree);
				all_vars.insert(fvs[tree].begin(), fvs[tree].end());
			}
			std::vector<raw_term> terms;
			// And make a pure TML formula listing them
			for(const sprawformtree &tree : ands) {
				std::set<elem> nv = set_intersection(fvs[tree],
					set_difference(all_vars, fvs[tree]));
				terms.push_back(to_pure_tml(tree, rp, nv));
			}
			// Make the representative rule and add to the program
			raw_rule nr(raw_term(part_id, fv), terms);
			rp.push_back(nr);
			break;
		} case elem::ALT: {
			// Collect all the disjuncts within the tree top
			std::vector<sprawformtree> alts;
			flatten_associative(elem::ALT, t, alts);
			for(const sprawformtree &tree : alts) {
				// Make a separate rule for each disjunct
				raw_rule nr(raw_term(part_id, fv), to_pure_tml(tree, rp, fv));
				rp.push_back(nr);
			}
			break;
		} case elem::NOT: {
			return to_pure_tml(t->l, rp, fv).negate();
		} case elem::EXISTS: {
			// Make the proposition that is being quantified
			std::set<elem> nfv = fv;
			const elem qvar = *(t->l->el);
			nfv.insert(qvar);
			raw_term nrt = to_pure_tml(t->r, rp, nfv);
			// Make the rule corresponding to this existential formula
			nfv.erase(qvar);
			raw_rule nr(raw_term(part_id, nfv), nrt);
			rp.push_back(nr);
			return raw_term(part_id, nfv);
		} case elem::UNIQUE: {
			// The uniqueness quantifier is logically equivalent to the
			// following
			const elem evar = elem::fresh_var(d), qvar = *(t->l->el);
			return to_pure_tml(std::make_shared<raw_form_tree>(elem::EXISTS,
				std::make_shared<raw_form_tree>(elem::VAR, evar),
				std::make_shared<raw_form_tree>(elem::FORALL,
					std::make_shared<raw_form_tree>(elem::VAR, qvar),
					std::make_shared<raw_form_tree>(elem::COIMPLIES, t->r,
						std::make_shared<raw_form_tree>(elem::NONE,
							raw_term(raw_term::EQ, { evar, elem_eq, qvar }))))), rp, fv);
		} case elem::NONE: {
			return *t->rt;
		} case elem::FORALL: {
			// The universal quantifier is logically equivalent to the
			// following
			elem qvar = *(t->l->el);
			return to_pure_tml(std::make_shared<raw_form_tree>(elem::NOT,
				std::make_shared<raw_form_tree>(elem::EXISTS,
					std::make_shared<raw_form_tree>(elem::VAR, qvar),
					std::make_shared<raw_form_tree>(elem::NOT, t->r))), rp, fv);
		} default:
			assert(false); //should never reach here
	}
	return raw_term(part_id, fv);
}

/* Convert every rule in the given program to pure TML rules. Rules with
 * multiple heads are also converted to multiple rules with single
 * heads. */

void driver::to_pure_tml(raw_prog &rp) {
	// Convert all FOL formulas to P-DATALOG
	for(int_t i = rp.r.size() - 1; i >= 0; i--) {
		raw_rule rr = rp.r[i];
		if(!rr.is_b()) {
			std::set<elem> nv;
			for(const raw_term &rt : rr.h) {
				collect_vars(rt, nv);
			}
			rr.set_b({{to_pure_tml(rr.prft, rp.r, nv)}});
		}
		rp.r[i] = rr;
	}
	// Split rules with multiple heads and delete those with 0 heads
	for(std::vector<raw_rule>::iterator it = rp.r.begin();
			it != rp.r.end();) {
		if(it->h.size() != 1) {
			// 0 heads are effectively eliminated, and multiple heads are
			// split up.
			const raw_rule rr = *it;
			it = rp.r.erase(it);
			for(const raw_term &rt : rr.h) {
				it = rp.r.insert(it, raw_rule(rt, rr.b));
			}
		} else {
			// Leave the single-headed rules alone.
			it++;
		}
	}
}

void driver::collect_free_vars(const std::vector<std::vector<raw_term>> &b,
		std::vector<elem> &bound_vars, std::set<elem> &free_vars) {
	for(const std::vector<raw_term> &bodie : b) {
		for(const raw_term &rt : bodie) {
			collect_free_vars(rt, bound_vars, free_vars);
		}
	}
}

/* Collect all the variables that are free in the given rule. */

void driver::collect_free_vars(const raw_rule &rr,
		std::set<elem> &free_vars) {
	std::vector<elem> bound_vars = {};
	for(const raw_term &rt : rr.h) {
		collect_free_vars(rt, bound_vars, free_vars);
	}
	if(rr.is_b()) {
		collect_free_vars(rr.b, bound_vars, free_vars);
	} else {
		collect_free_vars(rr.get_prft(), bound_vars, free_vars);
	}
}

std::set<elem> driver::collect_free_vars(const raw_rule &rr) {
	std::set<elem> free_vars;
	collect_free_vars(rr, free_vars);
	return free_vars;
}

/* Collect all the variables that are free in the given term. */

std::set<elem> driver::collect_free_vars(const raw_term &t) {
	std::set<elem> free_vars;
	std::vector<elem> bound_vars = {};
	collect_free_vars(t, bound_vars, free_vars);
	return free_vars;
}

void driver::collect_free_vars(const raw_term &t,
		std::vector<elem> &bound_vars, std::set<elem> &free_vars) {
	for(const elem &e : t.e) {
		if(e.type == elem::VAR) {
			free_vars.insert(e);
		}
	}
	for(const elem &bv : bound_vars) {
		free_vars.erase(bv);
	}
}

/* Collect all the variables that are free in the given tree. */

std::set<elem> driver::collect_free_vars(const sprawformtree &t) {
	std::set<elem> free_vars;
	std::vector<elem> bound_vars = {};
	collect_free_vars(t, bound_vars, free_vars);
	return free_vars;
}

void driver::collect_free_vars(const sprawformtree &t,
		std::vector<elem> &bound_vars, std::set<elem> &free_vars) {
	switch(t->type) {
		case elem::IMPLIES: case elem::COIMPLIES: case elem::AND:
		case elem::ALT:
			collect_free_vars(t->l, bound_vars, free_vars);
			collect_free_vars(t->r, bound_vars, free_vars);
			break;
		case elem::NOT:
			collect_free_vars(t->l, bound_vars, free_vars);
			break;
		case elem::EXISTS: case elem::UNIQUE: case elem::FORALL: {
			elem elt = *(t->l->el);
			bound_vars.push_back(elt);
			collect_free_vars(t->r, bound_vars, free_vars);
			bound_vars.pop_back();
			break;
		} case elem::NONE: {
			collect_free_vars(*t->rt, bound_vars, free_vars);
			break;
		} default:
			assert(false); //should never reach here
	}
}

string_t driver::generate_cpp(const elem &e, string_t &prog_constr, uint_t &cid, const string_t &dict_name, std::map<elem, string_t> &elem_cache) {
	if(elem_cache.find(e) != elem_cache.end()) {
		return elem_cache[e];
	}
	string_t e_name = to_string_t("e") + to_string_t(std::to_string(cid++).c_str());
	elem_cache[e] = e_name;
	prog_constr += to_string_t("elem ") + e_name + to_string_t(";\n");
	prog_constr += e_name + to_string_t(".type = ") + to_string_t(
		e.type == elem::NONE ? "elem::NONE" :
		e.type == elem::SYM ? "elem::SYM" :
		e.type == elem::NUM ? "elem::NUM" :
		e.type == elem::CHR ? "elem::CHR" :
		e.type == elem::VAR ? "elem::VAR" :
		e.type == elem::OPENP ? "elem::OPENP" :
		e.type == elem::CLOSEP ? "elem::CLOSEP" :
		e.type == elem::ALT ? "elem::ALT" :
		e.type == elem::STR ? "elem::STR" :
		e.type == elem::EQ ? "elem::EQ" :
		e.type == elem::NEQ ? "elem::NEQ" :
		e.type == elem::LEQ ? "elem::LEQ" :
		e.type == elem::GT ? "elem::GT" :
		e.type == elem::LT ? "elem::LT" :
		e.type == elem::GEQ ? "elem::GEQ" :
		e.type == elem::BLTIN ? "elem::BLTIN" :
		e.type == elem::NOT ? "elem::NOT" :
		e.type == elem::AND ? "elem::AND" :
		e.type == elem::OR ? "elem::OR" :
		e.type == elem::FORALL ? "elem::FORALL" :
		e.type == elem::EXISTS ? "elem::EXISTS" :
		e.type == elem::UNIQUE ? "elem::UNIQUE" :
		e.type == elem::IMPLIES ? "elem::IMPLIES" :
		e.type == elem::COIMPLIES ? "elem::COIMPLIES" :
		e.type == elem::ARITH ? "elem::ARITH" :
		e.type == elem::OPENB ? "elem::OPENB" :
		e.type == elem::CLOSEB ? "elem::CLOSEB" :
		e.type == elem::OPENSB ? "elem::OPENSB" :
		e.type == elem::CLOSESB ? "elem::CLOSESB" : "") + to_string_t(";\n");
	if(e.type == elem::CHR) {
		prog_constr += e_name + to_string_t(".ch = ") + to_string_t(std::to_string(e.ch).c_str()) + to_string_t(";\n");
	} else if(e.type == elem::NUM) {
		prog_constr += e_name + to_string_t(".num = ") + to_string_t(std::to_string(e.num).c_str()) + to_string_t(";\n");
	} else {
		prog_constr += e_name + to_string_t(".e = d.get_lexeme(\"") + lexeme2str(e.e) + to_string_t("\");\n");
	}
	return e_name;
}

string_t driver::generate_cpp(const raw_term &rt, string_t &prog_constr, uint_t &cid, const string_t &dict_name, std::map<elem, string_t> &elem_cache) {
	std::vector<string_t> elem_names;
	for(const elem &e : rt.e) {
		elem_names.push_back(generate_cpp(e, prog_constr, cid, dict_name, elem_cache));
	}
	string_t rt_name = to_string_t("rt") + to_string_t(std::to_string(cid++).c_str());
	prog_constr += to_string_t("raw_term ") + rt_name + to_string_t(";\n");
	prog_constr += rt_name + to_string_t(".neg = ") + to_string_t(rt.neg ? "true" : "false") + to_string_t(";\n");
	prog_constr += rt_name + to_string_t(".extype = ") + to_string_t(
		rt.extype == raw_term::REL ? "raw_term::REL" :
		rt.extype == raw_term::EQ ? "raw_term::EQ" :
		rt.extype == raw_term::LEQ ? "raw_term::LEQ" :
		rt.extype == raw_term::BLTIN ? "raw_term::BLTIN" :
		rt.extype == raw_term::ARITH ? "raw_term::ARITH" :
		rt.extype == raw_term::CONSTRAINT ? "raw_term::CONSTRAINT" : "") + to_string_t(";\n");
	for(const string_t &en : elem_names) {
		prog_constr += rt_name + to_string_t(".e.push_back(") + en + to_string_t(");\n");
	}
	prog_constr += rt_name + to_string_t(".calc_arity(nullptr);\n");
	return rt_name;
}

string_t driver::generate_cpp(const sprawformtree &t, string_t &prog_constr, uint_t &cid, const string_t &dict_name, std::map<elem, string_t> &elem_cache) {
	string_t ft_name = to_string_t("ft") + to_string_t(std::to_string(cid++).c_str());
	switch(t->type) {
		case elem::IMPLIES: case elem::COIMPLIES: case elem::AND:
		case elem::ALT: case elem::EXISTS: case elem::UNIQUE:
		case elem::FORALL: {
			string_t lft_name =
				generate_cpp(t->l, prog_constr, cid, dict_name, elem_cache);
			string_t rft_name = generate_cpp(t->r, prog_constr, cid, dict_name,
				elem_cache);
			string_t t_string = to_string_t(
				t->type == elem::IMPLIES ? "elem::IMPLIES" :
				t->type == elem::COIMPLIES ? "elem::COIMPLIES" :
				t->type == elem::AND ? "elem::AND" :
				t->type == elem::ALT ? "elem::ALT" :
				t->type == elem::EXISTS ? "elem::EXISTS" :
				t->type == elem::UNIQUE ? "elem::UNIQUE" :
				t->type == elem::FORALL ? "elem::FORALL" : "");
			prog_constr += to_string_t("sprawformtree ") + ft_name + to_string_t(" = "
				"std::make_shared<raw_form_tree>(") + t_string + to_string_t(", ") +
				lft_name + to_string_t(", ") + rft_name + to_string_t(");\n");
			break;
		} case elem::NOT: {
			string_t body_name = generate_cpp(t->l, prog_constr, cid, dict_name,
				elem_cache);
			prog_constr += to_string_t("sprawformtree ") + ft_name + to_string_t(" = "
				"std::make_shared<raw_form_tree>(elem::NOT, ") +
				body_name + to_string_t(");\n");
			break;
		} case elem::NONE: {
			string_t term_name = generate_cpp(*t->rt, prog_constr, cid, dict_name,
				elem_cache);
			prog_constr += to_string_t("sprawformtree ") + ft_name + to_string_t(" = "
				"std::make_shared<raw_form_tree>(elem::NONE, ") +
				term_name + to_string_t(");\n");
			break;
		} case elem::VAR: {
			string_t var_name = generate_cpp(*t->el, prog_constr, cid, dict_name,
				elem_cache);
			prog_constr += to_string_t("sprawformtree ") + ft_name + to_string_t(" = "
				"std::make_shared<raw_form_tree>(elem::VAR, ") +
				var_name + to_string_t(");\n");
			break;
		} default:
			assert(false); //should never reach here
	}
	return ft_name;
}

string_t driver::generate_cpp(const raw_rule &rr, string_t &prog_constr, uint_t &cid, const string_t &dict_name, std::map<elem, string_t> &elem_cache) {
	std::vector<string_t> term_names;
	for(const raw_term &rt : rr.h) {
		term_names.push_back(
			generate_cpp(rt, prog_constr, cid, dict_name, elem_cache));
	}
	string_t prft_name =
		generate_cpp(rr.get_prft(), prog_constr, cid, dict_name, elem_cache);
	string_t rule_name = to_string_t("rr") + to_string_t(std::to_string(cid++).c_str());
	prog_constr += to_string_t("raw_rule ") + rule_name + to_string_t(";\n");
	for(const string_t &tn : term_names) {
		prog_constr += rule_name + to_string_t(".h.push_back(") + tn + to_string_t(");\n");
	}
	if(!(rr.is_b() && rr.b.empty())) {
		prog_constr += rule_name + to_string_t(".set_prft(") + prft_name + to_string_t(");\n");
	}
	return rule_name;
}

string_t driver::generate_cpp(const raw_prog &rp, string_t &prog_constr, uint_t &cid, const string_t &dict_name, std::map<elem, string_t> &elem_cache) {
	std::vector<string_t> rule_names;
	for(const raw_rule &rr : rp.r) {
		rule_names.push_back(
			generate_cpp(rr, prog_constr, cid, dict_name, elem_cache));
	}
	string_t prog_name = to_string_t("rp") + to_string_t(std::to_string(cid++).c_str());
	prog_constr += to_string_t("raw_prog ") + prog_name + to_string_t(";\n");
	for(const string_t &rn : rule_names) {
		prog_constr += prog_name + to_string_t(".r.push_back(") + rn + to_string_t(");\n");
	}
	return prog_name;
}

/* Reduce the size of the universe that the given variable takes its values from
 * by statically analyzing the term and determining what is impossible. */

void driver::reduce_universe(const elem &var, const raw_term &rt,
		std::set<elem> &universe, idatabase &database) {
	if(rt.extype == raw_term::REL && !rt.neg) {
		if(database[get_relation_info(rt)].size() == 0) {
			universe.clear();
		} else {
			size_t var_pos;
			for(var_pos = 2; var_pos < rt.e.size() - 1 && rt.e[var_pos] != var; var_pos++);
			if(var_pos < rt.e.size() - 1) {
				std::set<elem> universe2;
				for(const raw_term &entry : database[get_relation_info(rt)]) {
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
				universe = universe2;
			}
		}
	}
}

/* Reduce the size of the universe that the given variable takes its values from
 * by statically analyzing the logical formula and determining what is
 * impossible. */
 
 void driver::reduce_universe(const elem &var,
		const std::vector<raw_term> &conj, std::set<elem> &universe,
		idatabase &database) {
	for(const raw_term &rt : conj) {
		reduce_universe(var, rt, universe, database);
	}
}

void driver::reduce_universe(const elem &var,
		const std::vector<std::vector<raw_term>> &disj,
		std::set<elem> &universe, idatabase &database) {
	if(!disj.empty()) {
		std::set<elem> universe_copy = universe;
		universe = {};
		for(const std::vector<raw_term> &conj : disj) {
			std::set<elem> reduced_universe = universe_copy;
			reduce_universe(var, conj, reduced_universe, database);
			universe.insert(reduced_universe.begin(), reduced_universe.end());
		}
	}
}

/* Reduce the size of the universe that the given variable takes its
 * values from by statically analyzing the rule and determining what is
 * impossible. */

void driver::reduce_universe(const elem &var, const raw_rule &rul,
		std::set<elem> &universe, idatabase &database) {
	reduce_universe(var, rul.b, universe, database);
}

/* Based on the current state of the database, use static analysis of
 * the logical formulas to remove from the universe of each quantification,
 * elements that could never satisfy their inner formula. */

void driver::populate_universes(const raw_rule &rul,
		std::set<elem> &universe, std::map<elem, std::set<elem>> &universes,
		idatabase &database) {
	const std::set<elem> &free_vars = collect_free_vars(rul);
	for(const elem &elt : free_vars) {
		std::set<elem> universe2 = universe;
		reduce_universe(elt, rul, universe2, database);
		universes[elt] = universe2;
	}
}

/* Evaluate the given logical term over the given database in the context
 * of the given bindings and return whether it is true or false. */

bool driver::evaluate_term(const raw_term &query,
		std::unordered_map<elem, elem, elem_hash> &bindings, idatabase &database) {
	if(query.extype == raw_term::REL) {
		raw_term query_substituted = query;
		query_substituted.neg = false;
		for(size_t i = 0; i < query.e.size(); i++) {
			if(query.e[i].type == elem::VAR) {
				query_substituted.e[i] = bindings[query.e[i]];
			}
		}
		raw_terms tab = database[get_relation_info(query)];
		if(tab.find(query_substituted) != tab.end()) {
			return !query.neg;
		} else {
			return query.neg;
		}
	} else if(query.extype == raw_term::EQ) {
		elem lhs = query.e[0], rhs = query.e[2];
		if(lhs.type == elem::VAR) lhs = bindings[lhs];
		if(rhs.type == elem::VAR) rhs = bindings[rhs];
		return (lhs == rhs) != query.neg;
	}
	assert(false); //should never reach here
}

/* Evaluate the given logical formula over the given database in the
 * context of the given bindings and return whether it is true or false.
 * The universes parameter is used to obtain the domain for each
 * quantification. */

bool driver::evaluate_conjunction(const std::vector<raw_term> &conj,
		std::unordered_map<elem, elem, elem_hash> &bindings, idatabase &database) {
	bool succ = true;
	for(const raw_term &t : conj) {
		succ &= evaluate_term(t, bindings, database);
	}
	return succ;
}

bool driver::evaluate_disjunction(const std::vector<std::vector<raw_term>> &disj,
		std::unordered_map<elem, elem, elem_hash> &bindings, idatabase &database) {
	if(disj.empty()) {
		return true;
	} else {
		bool succ = false;
		for(const std::vector<raw_term> &conj : disj) {
			succ |= evaluate_conjunction(conj, bindings, database);
		}
		return succ;
	}
}

/* Interpret a rule. That is, run a rule over the current databaseand add the
 * discovered facts to the database. */

void driver::interpret_rule(size_t hd_idx, std::set<elem> &free_vars,
		const raw_rule &rul, const std::map<elem, std::set<elem>> &universes,
		std::unordered_map<elem, elem, elem_hash> &bindings, idatabase &database,
		idatabase &next_database) {
	const raw_term &head = rul.h[hd_idx];
	if(!free_vars.empty()) {
		const elem var = *free_vars.begin();
		free_vars.erase(var);
		for(const elem &elt : universes.at(var)) {
			bindings[var] = elt;
			interpret_rule(hd_idx, free_vars, rul, universes, bindings, database, next_database);
		}
		free_vars.insert(var);
	} else if(evaluate_disjunction(rul.b, bindings, database)) {
		raw_term fact = head;
		for(elem &e : fact.e) {
			if(e.type == elem::VAR) {
				e = bindings[e];
			}
		}
		if(head.neg) {
			fact.neg = false;
			next_database[get_relation_info(fact)].erase(fact);
		} else {
			next_database[get_relation_info(fact)].insert(fact);
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

void driver::populate_universe(const raw_prog &rp,
		std::set<elem> &universe) {
	for(const raw_rule &rr : rp.r) {
		for(const raw_term &rt : rr.h) {
			populate_universe(rt, universe);
		}
		for(const std::vector<raw_term> bodie : rr.b) {
			for(const raw_term &rt : bodie) {
				populate_universe(rt, universe);
			}
		}
	}
}

void driver::print_database(const idatabase &database) {
	for(const auto &[ri, tab] : database) {
		for(const raw_term &entry : tab) {
			std::cout << entry << "." << std::endl;
		}
	}
}

void driver::naive_pfp(const raw_prog &rp, std::set<elem> &universe,
		idatabase &database) {
	populate_universe(rp, universe);
	idatabase prev_database;
	std::vector<idatabase> stages;
	// Interpret program
	do {
		std::cout << "Step:" << std::endl;
		print_database(database);
		std::cout << std::endl << std::endl;
		stages.push_back(database);
		prev_database = database;
		for(const raw_rule &rr : rp.r) {
			for(size_t hd_idx = 0; hd_idx < rr.h.size(); hd_idx++) {
				std::map<elem, std::set<elem>> universes;
				populate_universes(rr, universe, universes, prev_database);
				std::unordered_map<elem, elem, elem_hash> bindings;
				std::set<elem> free_vars = collect_free_vars(rr);
				interpret_rule(hd_idx, free_vars, rr, universes, bindings, prev_database, database);
			}
		}
	} while(std::find(stages.begin(), stages.end(), database) == stages.end());
}

bool driver::transform(raw_prog& rp, const strs_t& /*strtrees*/) {
	lexeme trel = { 0, 0 };
	directives_load(rp, trel);
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
	get_all_vars(rp);
//	for (auto x : pd.strs)
//		if (!has(transformed_strings, x.first))
//			transform_string(x.second, rp.p[n], x.first),
//			transformed_strings.insert(x.first);
//	for (auto x : strtrees)
//		if (!has(transformed_strings, x.first))
//			transform_string(x.second, rp.p[n], x.first),
//			transformed_strings.insert(x.first);
	if (!rp.g.empty()) //{
		if (pd.strs.size() > 1)
			return throw_runtime_error(err_one_input);
//		else transform_grammar(rp.p[n], pd.strs.begin()->first,
//			pd.strs.begin()->second.size());
//	}
//	if (opts.enabled("sdt"))
//		for (raw_prog& p : rp.p)
//			p = transform_sdt(move(p));
	static std::set<raw_prog *> transformed_progs;
	if(transformed_progs.find(&rp) == transformed_progs.end()) {
		transformed_progs.insert(&rp);
		simplify_formulas(rp);
		std::cout << "Simplified Program:" << std::endl << std::endl << rp << std::endl;
		std::cout << "Program Generator:" << std::endl << std::endl;
		uint_t cid = 0;
		string_t rp_generator;
		std::map<elem, string_t> elem_cache;
		generate_cpp(rp, rp_generator, cid, to_string_t("d"), elem_cache);
		std::cout << to_string(rp_generator) << std::endl << std::endl;
		transform_quotes(rp);
		std::cout << "Quoted Program:" << std::endl << std::endl << rp << std::endl;
		transform_evals(rp);
		std::cout << "Evaled Program:" << std::endl << std::endl << rp << std::endl;
		//quote_prog(rp, elem(elem::SYM, get_lexeme("this")), rp);
		//std::cout << "TML Program With this:" << std::endl << std::endl << rp << std::endl;
		step_transform(rp, [&](raw_prog &rp) {
			to_pure_tml(rp);
			std::cout << "Pure TML Program:" << std::endl << std::endl << rp << std::endl;
			//subsume_queries(rp);
			std::cout << "Minimized Program:" << std::endl << std::endl << rp << std::endl;
			//factor_rules(rp);
			std::cout << "Factorized Program:" << std::endl << std::endl << rp << std::endl;
		});
		std::cout << "Step Transformed Program:" << std::endl << std::endl << rp << std::endl;
		std::set<elem> universe;
		idatabase database;
		//naive_pfp(rp, universe, database);
		//std::cout << "Fixed Point:" << std::endl << std::endl;
		//print_database(database);
	}
	std::cout << std::endl << std::endl;
#ifdef TRANSFORM_BIN_DRIVER
	if (opts.enabled("bin"))
		for (raw_prog& p : rp.p)
			transform_bin(p);
#endif
//	if (trel[0]) transform_proofs(rp.p[n], trel);
	//o::out()<<rp.p[n]<<endl;
//	if (pd.bwd) rp.p.push_back(transform_bwd(rp.p[n]));
	for (auto& np : rp.nps) if (!transform(np, pd.strs)) return false;
	return true;
}

void driver::output_pl(const raw_prog& p) const {
	if (opts.enabled("xsb"))     print_xsb(o::to("xsb"), p);
	if (opts.enabled("swipl"))   print_swipl(o::to("swipl"), p);
	if (opts.enabled("souffle")) print_souffle(o::to("souffle"), p);
}

bool driver::prog_run(raw_prog& p, size_t steps, size_t break_on_step) {
//	pd.clear();
	//DBG(o::out() << "original program:"<<endl<<p;)
//	strtrees.clear(), get_dict_stats(rp.p[n]), add_rules(rp.p[n]);
	clock_t start, end;
	size_t step = nsteps();
	measure_time_start();
	if (opts.enabled("guards")) {
		tbl->transform_guards(p);
		if (opts.enabled("transformed")) o::to("transformed")
			<< "after transform_guards:\n" << p << endl<<endl;
	}
	bool fp = tbl->run_prog(p, pd.strs, steps, break_on_step);
	o::ms() << "# elapsed: ";
	measure_time_end();
	if (tbl->error) error = true;
	pd.elapsed_steps = nsteps() - step;
//	for (auto x : prog->strtrees_out)
//		strtrees.emplace(x.first, get_trees(prog->pd.strtrees[x.first],
//					x.second, prog->rng.bits));
	return fp;
}

bool driver::add(input* in) {
	if (!rp.parse(in, tbl->get_dict())) return !(error = true);
	transform(rp.p, pd.strs);
	return true;
}

template <typename T>
void driver::list(std::basic_ostream<T>& os, size_t /*n*/) {
	os << rp.p << endl;
}
template void driver::list(std::basic_ostream<char>&, size_t);
template void driver::list(std::basic_ostream<wchar_t>&, size_t);

void driver::restart() {
	pd.n = 0;
	pd.start_step = nsteps();
	running = true;
}

bool driver::run(size_t steps, size_t break_on_step) {
	if (!running) restart();
	if (nsteps() == pd.start_step) {
		//transform(rp.p, pd.strs);
		for (const string& s : str_bltins)
			rp.p.builtins.insert(get_lexeme(s));
		output_pl(rp.p);
	}
	if (opts.disabled("run") && opts.disabled("repl")) return true;
	bool fp = prog_run(rp.p, steps, break_on_step);
	if (fp) result = true;
	return fp;
}

bool driver::step(size_t steps, size_t break_on_step) {
	return run(steps, break_on_step);
}

template <typename T>
void driver::info(std::basic_ostream<T>& os) {
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
		opts.enabled("t"), opts.enabled("regex"), opts.enabled("kg"));
	set_print_step(opts.enabled("ps"));
	set_print_updates(opts.enabled("pu"));
	set_populate_tml_update(opts.enabled("tml_update"));
	set_regex_level(opts.get_int("regex-level"));
	if (!ii) return;
	current_input = ii->first();
	if (current_input && !add(current_input)) return;
	read_inputs();
}

driver::driver(FILE *f, const options &o) : driver(input::file_read_text(f),o){}
driver::driver(string_t s, const options& o)    : driver(to_string(s), o) {}
driver::driver(const char *s, const options &o) : driver(string(s), o) {}
driver::driver(ccs   s, const options &o)       : driver(string_t(s), o) {}
driver::driver(const options &o)                : driver(string(), o) {}
driver::driver(string s)                        : driver(s, options()) {}
driver::driver(FILE *f)                         : driver(f, options()) {}
driver::driver(string_t s)                      : driver(to_string(s)) {}
driver::driver(const char *s)                   : driver(s, options()) {}
driver::driver(ccs s)                           : driver(string_t(s)) {}

driver::~driver() {
	if (tbl) delete tbl;
	for (auto x : strs_allocated) free((char *)x);
}
