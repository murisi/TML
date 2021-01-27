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

void driver::make_domain(raw_prog &rp, const elem &out_rel,
		std::set<elem> elts, int_t max_size, int_t rest_id, int_t &curr_id) {
	if(max_size > 0) {
		for(const elem &elt : elts) {
			rp.r.push_back(raw_term({ out_rel, elem_openp, elem(curr_id++), elt,
				elem(rest_id), elem_closep }));
			make_domain(rp, out_rel, elts, max_size - 1, curr_id - 1, curr_id);
		}
	}
}

/* Loop through the rules of the given program checking if they use a
 * function called "domain" in their bodies. Domain's first argument is
 * the relation into which it should put the domain it creates, and
 * it's second argument is the program to quote. */

void driver::transform_domains(raw_prog &rp) {
	for(size_t oridx = 0; oridx < rp.r.size(); oridx++) {
		// Iterate through the bodies of the current rule looking for uses
		// of the "eval" relation.
		for(const raw_term &curr_term : rp.r[oridx].h) {
			if(!(!curr_term.e.empty() && curr_term.e[0].type == elem::SYM &&
				to_string_t("domain") == lexeme2str(curr_term.e[0].e))) continue;
			// The first parenthesis marks the beginning of eval's three arguments.
			//if(!(ssize(curr_term.e) == 6 && curr_term.e[1].type == elem::OPENP &&
			//	curr_term.e[5].type == elem::CLOSEP)) continue;
			// The relation to contain the evaled relation is the first symbol
			// between the parentheses
			elem out_rel = curr_term.e[2];
			// The maximum arity of the desired domain is the first symbol
			// between the inner parentheses
			int_t max_arity = curr_term.e[4].num;
			// The number of times the linked lists should be nested is the
			// second symbol between the inner parentheses
			int_t nesting = curr_term.e[5].num;
			// This transformation will automatically generate non-negative
			// numbers up to this limit for inclusion in domain
			int_t gen_limit = curr_term.e[6].num;
			// After the above triple comes the list of symbols to be included
			// in the desired domain
			std::set<elem> elts;
			for(int_t idx = 8; idx < curr_term.e.size() - 1; idx++) {
				elts.insert(curr_term.e[idx]);
			}
			for(int_t nat = 0; nat < gen_limit; nat++) {
				elts.insert(elem(nat));
			}
			int_t curr_id = 1;
			rp.r.push_back(raw_term({ out_rel, elem_openp, elem(0), elem_closep }));
			make_domain(rp, out_rel, elts, max_arity, 0, curr_id);
			
			/*elem quote_str = curr_term.e[4];
			
			if(quote_str.type == elem::STR && quote_str.e[1] > quote_str.e[0] &&
					*quote_str.e[0] == '`') {
				raw_prog nrp = read_prog(quote_str, rp);
				// Create the quotation relation
				quote_prog(nrp, out_rel, domain_sym, rp);
			}*/
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

/* In the case that the argument is a variable, get the symbol
 * associated with it and return that. If there is no such association,
 * make one such that it uses the lowest 0-based index. */

elem driver::numeric_quote_elem(const elem &e,
		std::map<elem, elem> &variables) {
	if(e.type == elem::VAR) {
		if(variables.find(e) != variables.end()) {
			return variables[e];
		} else {
			// Since the current variable lacks a designated substitute,
			// make one and record the mapping.
			return variables[e] = elem(int_t(variables.size()));
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
		elem elems_id = elem::fresh_var(d), tags_id = elem::fresh_var(d),
			elems_hid = elems_id, tags_hid = tags_id;
		std::vector<raw_term> quote_body;
		for(int_t param_idx = 2; param_idx < ssize(head.e) - 1; param_idx ++) {
			elem next_elems_id = elem::fresh_var(d),
				next_tags_id = elem::fresh_var(d);
			quote_body.push_back(raw_term({domain_name, elem_openp, elems_id,
				numeric_quote_elem(head.e[param_idx], variables), next_elems_id,
				elem_closep}));
			quote_body.push_back(raw_term({domain_name, elem_openp, tags_id,
				elem(int_t(head.e[param_idx].type == elem::VAR)), next_tags_id,
				elem_closep}));
			elems_id = next_elems_id;
			tags_id = next_tags_id;
		}
		quote_body.push_back(raw_term({domain_name, elem_openp, elems_id,
			elem_closep}));
		quote_body.push_back(raw_term({domain_name, elem_openp, tags_id,
			elem_closep}));
		// Add metadata to quoted term: term signature, term id, term name
		raw_rule quote(raw_term({rel_name, elem_openp, elem(QTERM),
			term_id, head.e[0], elems_hid, tags_hid, elem_closep }), quote_body);
		rp.r.push_back(quote);
	} else if(head.extype == raw_term::EQ) {
		// Add metadata to quoted term: term signature, term id, term name
		std::vector<elem> quoted_term_e = {rel_name, elem_openp, elem(QEQUALS),
			term_id, numeric_quote_elem(head.e[0], variables),
			numeric_quote_elem(head.e[2], variables),
			int_t(head.e[0].type == elem::VAR), int_t(head.e[2].type == elem::VAR),
			elem_closep };
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
		const elem &rel_name, const elem &domain_name, raw_prog &rp) {
	// Get dictionary for generating fresh symbols
	dict_t &d = tbl->get_dict();
	// Maintain a list of the variable substitutions:
	std::map<elem, elem> variables;
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
	for(int_t ridx = 0; ridx < ssize(nrp.r); ridx++) {
		quote_rule(nrp.r[ridx], rel_name, domain_name, rp);
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
				elem e7(int_t(QTERM));
				elem e8;
				e8.type = elem::VAR;
				e8.e = d.get_lexeme("?nm");
				elem e9;
				e9.type = elem::VAR;
				e9.e = d.get_lexeme("?args");
				elem e10;
				e10.type = elem::VAR;
				e10.e = d.get_lexeme("?vars");
				raw_term rt11;
				rt11.neg = false;
				rt11.extype = raw_term::REL;
				rt11.e.push_back(e6);
				rt11.e.push_back(e1);
				rt11.e.push_back(e7);
				rt11.e.push_back(e2);
				rt11.e.push_back(e8);
				rt11.e.push_back(e9);
				rt11.e.push_back(e10);
				rt11.e.push_back(e3);
				rt11.calc_arity(nullptr);
				sprawformtree ft5 = std::make_shared<raw_form_tree>(elem::NONE, rt11);
				raw_rule rr12;
				rr12.h.push_back(rt4);
				rr12.set_prft(ft5);
				raw_term rt13;
				rt13.neg = false;
				rt13.extype = raw_term::REL;
				rt13.e.push_back(e0);
				rt13.e.push_back(e1);
				rt13.e.push_back(e2);
				rt13.e.push_back(e3);
				rt13.calc_arity(nullptr);
				elem e15(int_t(QEQUALS));
				elem e16;
				e16.type = elem::VAR;
				e16.e = d.get_lexeme("?p1");
				elem e17;
				e17.type = elem::VAR;
				e17.e = d.get_lexeme("?p2");
				raw_term rt18;
				rt18.neg = false;
				rt18.extype = raw_term::REL;
				rt18.e.push_back(e6);
				rt18.e.push_back(e1);
				rt18.e.push_back(e15);
				rt18.e.push_back(e2);
				rt18.e.push_back(e16);
				rt18.e.push_back(e17);
				rt18.e.push_back(e3);
				rt18.calc_arity(nullptr);
				sprawformtree ft14 = std::make_shared<raw_form_tree>(elem::NONE, rt18);
				raw_rule rr19;
				rr19.h.push_back(rt13);
				rr19.set_prft(ft14);
				raw_term rt20;
				rt20.neg = false;
				rt20.extype = raw_term::REL;
				rt20.e.push_back(e0);
				rt20.e.push_back(e1);
				rt20.e.push_back(e2);
				rt20.e.push_back(e3);
				rt20.calc_arity(nullptr);
				elem e22(int_t(QAND));
				elem e23;
				e23.type = elem::VAR;
				e23.e = d.get_lexeme("?b1");
				elem e24;
				e24.type = elem::VAR;
				e24.e = d.get_lexeme("?b2");
				raw_term rt25;
				rt25.neg = false;
				rt25.extype = raw_term::REL;
				rt25.e.push_back(e6);
				rt25.e.push_back(e1);
				rt25.e.push_back(e22);
				rt25.e.push_back(e2);
				rt25.e.push_back(e23);
				rt25.e.push_back(e24);
				rt25.e.push_back(e3);
				rt25.calc_arity(nullptr);
				sprawformtree ft21 = std::make_shared<raw_form_tree>(elem::NONE, rt25);
				raw_rule rr26;
				rr26.h.push_back(rt20);
				rr26.set_prft(ft21);
				raw_term rt27;
				rt27.neg = false;
				rt27.extype = raw_term::REL;
				rt27.e.push_back(e0);
				rt27.e.push_back(e1);
				rt27.e.push_back(e2);
				rt27.e.push_back(e3);
				rt27.calc_arity(nullptr);
				elem e29(int_t(QALT));
				raw_term rt30;
				rt30.neg = false;
				rt30.extype = raw_term::REL;
				rt30.e.push_back(e6);
				rt30.e.push_back(e1);
				rt30.e.push_back(e29);
				rt30.e.push_back(e2);
				rt30.e.push_back(e23);
				rt30.e.push_back(e24);
				rt30.e.push_back(e3);
				rt30.calc_arity(nullptr);
				sprawformtree ft28 = std::make_shared<raw_form_tree>(elem::NONE, rt30);
				raw_rule rr31;
				rr31.h.push_back(rt27);
				rr31.set_prft(ft28);
				raw_term rt32;
				rt32.neg = false;
				rt32.extype = raw_term::REL;
				rt32.e.push_back(e0);
				rt32.e.push_back(e1);
				rt32.e.push_back(e2);
				rt32.e.push_back(e3);
				rt32.calc_arity(nullptr);
				elem e34(int_t(QTRUE));
				raw_term rt35;
				rt35.neg = false;
				rt35.extype = raw_term::REL;
				rt35.e.push_back(e6);
				rt35.e.push_back(e1);
				rt35.e.push_back(e34);
				rt35.e.push_back(e2);
				rt35.e.push_back(e3);
				rt35.calc_arity(nullptr);
				sprawformtree ft33 = std::make_shared<raw_form_tree>(elem::NONE, rt35);
				raw_rule rr36;
				rr36.h.push_back(rt32);
				rr36.set_prft(ft33);
				elem e37;
				e37.type = elem::SYM;
				e37.e = d.get_lexeme("RULE_NODE");
				raw_term rt38;
				rt38.neg = false;
				rt38.extype = raw_term::REL;
				rt38.e.push_back(e37);
				rt38.e.push_back(e1);
				rt38.e.push_back(e2);
				rt38.e.push_back(e3);
				rt38.calc_arity(nullptr);
				elem e40(int_t(QRULE));
				elem e41;
				e41.type = elem::VAR;
				e41.e = d.get_lexeme("?h");
				elem e42;
				e42.type = elem::VAR;
				e42.e = d.get_lexeme("?b");
				raw_term rt43;
				rt43.neg = false;
				rt43.extype = raw_term::REL;
				rt43.e.push_back(e6);
				rt43.e.push_back(e1);
				rt43.e.push_back(e40);
				rt43.e.push_back(e2);
				rt43.e.push_back(e41);
				rt43.e.push_back(e42);
				rt43.e.push_back(e3);
				rt43.calc_arity(nullptr);
				sprawformtree ft39 = std::make_shared<raw_form_tree>(elem::NONE, rt43);
				raw_rule rr44;
				rr44.h.push_back(rt38);
				rr44.set_prft(ft39);
				elem e45;
				e45.type = elem::SYM;
				e45.e = d.get_lexeme("COMMIT");
				raw_term rt46;
				rt46.neg = false;
				rt46.extype = raw_term::REL;
				rt46.e.push_back(e45);
				rt46.e.push_back(e1);
				rt46.e.push_back(e3);
				rt46.calc_arity(nullptr);
				elem e47;
				e47.type = elem::SYM;
				e47.e = d.get_lexeme("EXECUTE");
				raw_term rt48;
				rt48.neg = true;
				rt48.extype = raw_term::REL;
				rt48.e.push_back(e47);
				rt48.e.push_back(e1);
				rt48.e.push_back(e3);
				rt48.calc_arity(nullptr);
				elem e49;
				e49.type = elem::SYM;
				e49.e = d.get_lexeme("RULE_DONE");
				elem e50;
				e50.type = elem::VAR;
				e50.e = d.get_lexeme("?y");
				raw_term rt51;
				rt51.neg = true;
				rt51.extype = raw_term::REL;
				rt51.e.push_back(e49);
				rt51.e.push_back(e1);
				rt51.e.push_back(e50);
				rt51.e.push_back(e3);
				rt51.calc_arity(nullptr);
				elem e55;
				e55.type = elem::SYM;
				e55.e = d.get_lexeme("EXECUTE2");
				raw_term rt56;
				rt56.neg = false;
				rt56.extype = raw_term::REL;
				rt56.e.push_back(e55);
				rt56.e.push_back(e1);
				rt56.e.push_back(e3);
				rt56.calc_arity(nullptr);
				sprawformtree ft54 = std::make_shared<raw_form_tree>(elem::NONE, rt56);
				raw_term rt59;
				rt59.neg = false;
				rt59.extype = raw_term::REL;
				rt59.e.push_back(e45);
				rt59.e.push_back(e1);
				rt59.e.push_back(e3);
				rt59.calc_arity(nullptr);
				sprawformtree ft58 = std::make_shared<raw_form_tree>(elem::NONE, rt59);
				sprawformtree ft57 = std::make_shared<raw_form_tree>(elem::NOT, ft58);
				sprawformtree ft53 = std::make_shared<raw_form_tree>(elem::AND, ft54, ft57);
				elem e62;
				e62.type = elem::VAR;
				e62.e = d.get_lexeme("?x");
				sprawformtree ft61 = std::make_shared<raw_form_tree>(elem::VAR, e62);
				elem e65;
				e65.type = elem::VAR;
				e65.e = d.get_lexeme("?z");
				sprawformtree ft64 = std::make_shared<raw_form_tree>(elem::VAR, e65);
				raw_term rt68;
				rt68.neg = false;
				rt68.extype = raw_term::REL;
				rt68.e.push_back(e0);
				rt68.e.push_back(e1);
				rt68.e.push_back(e62);
				rt68.e.push_back(e3);
				rt68.calc_arity(nullptr);
				sprawformtree ft67 = std::make_shared<raw_form_tree>(elem::NONE, rt68);
				elem e70;
				e70.type = elem::SYM;
				e70.e = d.get_lexeme("FORMULA_DONE");
				raw_term rt71;
				rt71.neg = false;
				rt71.extype = raw_term::REL;
				rt71.e.push_back(e70);
				rt71.e.push_back(e1);
				rt71.e.push_back(e62);
				rt71.e.push_back(e65);
				rt71.e.push_back(e3);
				rt71.calc_arity(nullptr);
				sprawformtree ft69 = std::make_shared<raw_form_tree>(elem::NONE, rt71);
				sprawformtree ft66 = std::make_shared<raw_form_tree>(elem::IMPLIES, ft67, ft69);
				sprawformtree ft63 = std::make_shared<raw_form_tree>(elem::EXISTS, ft64, ft66);
				sprawformtree ft60 = std::make_shared<raw_form_tree>(elem::FORALL, ft61, ft63);
				sprawformtree ft52 = std::make_shared<raw_form_tree>(elem::AND, ft53, ft60);
				raw_rule rr72;
				rr72.h.push_back(rt46);
				rr72.h.push_back(rt48);
				rr72.h.push_back(rt51);
				rr72.set_prft(ft52);
				elem e73;
				e73.type = elem::SYM;
				e73.e = d.get_lexeme("COMMIT2");
				raw_term rt74;
				rt74.neg = false;
				rt74.extype = raw_term::REL;
				rt74.e.push_back(e73);
				rt74.e.push_back(e1);
				rt74.e.push_back(e3);
				rt74.calc_arity(nullptr);
				raw_term rt76;
				rt76.neg = false;
				rt76.extype = raw_term::REL;
				rt76.e.push_back(e45);
				rt76.e.push_back(e1);
				rt76.e.push_back(e3);
				rt76.calc_arity(nullptr);
				sprawformtree ft75 = std::make_shared<raw_form_tree>(elem::NONE, rt76);
				raw_rule rr77;
				rr77.h.push_back(rt74);
				rr77.set_prft(ft75);
				raw_term rt78;
				rt78.neg = true;
				rt78.extype = raw_term::REL;
				rt78.e.push_back(e55);
				rt78.e.push_back(e1);
				rt78.e.push_back(e3);
				rt78.calc_arity(nullptr);
				raw_term rt80;
				rt80.neg = false;
				rt80.extype = raw_term::REL;
				rt80.e.push_back(e45);
				rt80.e.push_back(e1);
				rt80.e.push_back(e3);
				rt80.calc_arity(nullptr);
				sprawformtree ft79 = std::make_shared<raw_form_tree>(elem::NONE, rt80);
				raw_rule rr81;
				rr81.h.push_back(rt78);
				rr81.set_prft(ft79);
				raw_term rt82;
				rt82.neg = false;
				rt82.extype = raw_term::REL;
				rt82.e.push_back(e47);
				rt82.e.push_back(e1);
				rt82.e.push_back(e3);
				rt82.calc_arity(nullptr);
				raw_term rt83;
				rt83.neg = true;
				rt83.extype = raw_term::REL;
				rt83.e.push_back(e45);
				rt83.e.push_back(e1);
				rt83.e.push_back(e3);
				rt83.calc_arity(nullptr);
				raw_term rt84;
				rt84.neg = true;
				rt84.extype = raw_term::REL;
				rt84.e.push_back(e70);
				rt84.e.push_back(e1);
				rt84.e.push_back(e50);
				rt84.e.push_back(e3);
				rt84.calc_arity(nullptr);
				raw_term rt88;
				rt88.neg = false;
				rt88.extype = raw_term::REL;
				rt88.e.push_back(e73);
				rt88.e.push_back(e1);
				rt88.e.push_back(e3);
				rt88.calc_arity(nullptr);
				sprawformtree ft87 = std::make_shared<raw_form_tree>(elem::NONE, rt88);
				raw_term rt91;
				rt91.neg = false;
				rt91.extype = raw_term::REL;
				rt91.e.push_back(e47);
				rt91.e.push_back(e1);
				rt91.e.push_back(e3);
				rt91.calc_arity(nullptr);
				sprawformtree ft90 = std::make_shared<raw_form_tree>(elem::NONE, rt91);
				sprawformtree ft89 = std::make_shared<raw_form_tree>(elem::NOT, ft90);
				sprawformtree ft86 = std::make_shared<raw_form_tree>(elem::AND, ft87, ft89);
				sprawformtree ft93 = std::make_shared<raw_form_tree>(elem::VAR, e62);
				raw_term rt96;
				rt96.neg = false;
				rt96.extype = raw_term::REL;
				rt96.e.push_back(e37);
				rt96.e.push_back(e1);
				rt96.e.push_back(e62);
				rt96.e.push_back(e3);
				rt96.calc_arity(nullptr);
				sprawformtree ft95 = std::make_shared<raw_form_tree>(elem::NONE, rt96);
				raw_term rt98;
				rt98.neg = false;
				rt98.extype = raw_term::REL;
				rt98.e.push_back(e49);
				rt98.e.push_back(e1);
				rt98.e.push_back(e62);
				rt98.e.push_back(e3);
				rt98.calc_arity(nullptr);
				sprawformtree ft97 = std::make_shared<raw_form_tree>(elem::NONE, rt98);
				sprawformtree ft94 = std::make_shared<raw_form_tree>(elem::IMPLIES, ft95, ft97);
				sprawformtree ft92 = std::make_shared<raw_form_tree>(elem::FORALL, ft93, ft94);
				sprawformtree ft85 = std::make_shared<raw_form_tree>(elem::AND, ft86, ft92);
				raw_rule rr99;
				rr99.h.push_back(rt82);
				rr99.h.push_back(rt83);
				rr99.h.push_back(rt84);
				rr99.set_prft(ft85);
				raw_term rt100;
				rt100.neg = false;
				rt100.extype = raw_term::REL;
				rt100.e.push_back(e55);
				rt100.e.push_back(e1);
				rt100.e.push_back(e3);
				rt100.calc_arity(nullptr);
				raw_term rt102;
				rt102.neg = false;
				rt102.extype = raw_term::REL;
				rt102.e.push_back(e47);
				rt102.e.push_back(e1);
				rt102.e.push_back(e3);
				rt102.calc_arity(nullptr);
				sprawformtree ft101 = std::make_shared<raw_form_tree>(elem::NONE, rt102);
				raw_rule rr103;
				rr103.h.push_back(rt100);
				rr103.set_prft(ft101);
				raw_term rt104;
				rt104.neg = true;
				rt104.extype = raw_term::REL;
				rt104.e.push_back(e73);
				rt104.e.push_back(e1);
				rt104.e.push_back(e3);
				rt104.calc_arity(nullptr);
				raw_term rt106;
				rt106.neg = false;
				rt106.extype = raw_term::REL;
				rt106.e.push_back(e47);
				rt106.e.push_back(e1);
				rt106.e.push_back(e3);
				rt106.calc_arity(nullptr);
				sprawformtree ft105 = std::make_shared<raw_form_tree>(elem::NONE, rt106);
				raw_rule rr107;
				rr107.h.push_back(rt104);
				rr107.set_prft(ft105);
				elem e108;
				e108.type = elem::SYM;
				e108.e = d.get_lexeme("COUNTDOWN0");
				raw_term rt109;
				rt109.neg = false;
				rt109.extype = raw_term::REL;
				rt109.e.push_back(e108);
				rt109.e.push_back(e1);
				rt109.e.push_back(e3);
				rt109.calc_arity(nullptr);
				elem e111;
				e111.type = elem::NUM;
				e111.num = 0;
				elem e112;
				e112.type = elem::EQ;
				e112.e = d.get_lexeme("=");
				raw_term rt113;
				rt113.neg = false;
				rt113.extype = raw_term::EQ;
				rt113.e.push_back(e111);
				rt113.e.push_back(e112);
				rt113.e.push_back(e111);
				rt113.calc_arity(nullptr);
				sprawformtree ft110 = std::make_shared<raw_form_tree>(elem::NONE, rt113);
				raw_rule rr114;
				rr114.h.push_back(rt109);
				elem e115;
				e115.type = elem::SYM;
				e115.e = d.get_lexeme("COUNTDOWN1");
				raw_term rt116;
				rt116.neg = false;
				rt116.extype = raw_term::REL;
				rt116.e.push_back(e115);
				rt116.e.push_back(e1);
				rt116.e.push_back(e3);
				rt116.calc_arity(nullptr);
				raw_term rt118;
				rt118.neg = false;
				rt118.extype = raw_term::REL;
				rt118.e.push_back(e108);
				rt118.e.push_back(e1);
				rt118.e.push_back(e3);
				rt118.calc_arity(nullptr);
				sprawformtree ft117 = std::make_shared<raw_form_tree>(elem::NONE, rt118);
				raw_rule rr119;
				rr119.h.push_back(rt116);
				rr119.set_prft(ft117);
				elem e120;
				e120.type = elem::SYM;
				e120.e = d.get_lexeme("COUNTDOWN2");
				raw_term rt121;
				rt121.neg = false;
				rt121.extype = raw_term::REL;
				rt121.e.push_back(e120);
				rt121.e.push_back(e1);
				rt121.e.push_back(e3);
				rt121.calc_arity(nullptr);
				raw_term rt123;
				rt123.neg = false;
				rt123.extype = raw_term::REL;
				rt123.e.push_back(e115);
				rt123.e.push_back(e1);
				rt123.e.push_back(e3);
				rt123.calc_arity(nullptr);
				sprawformtree ft122 = std::make_shared<raw_form_tree>(elem::NONE, rt123);
				raw_rule rr124;
				rr124.h.push_back(rt121);
				rr124.set_prft(ft122);
				elem e125;
				e125.type = elem::SYM;
				e125.e = d.get_lexeme("COUNTDOWN3");
				raw_term rt126;
				rt126.neg = false;
				rt126.extype = raw_term::REL;
				rt126.e.push_back(e125);
				rt126.e.push_back(e1);
				rt126.e.push_back(e3);
				rt126.calc_arity(nullptr);
				raw_term rt128;
				rt128.neg = false;
				rt128.extype = raw_term::REL;
				rt128.e.push_back(e120);
				rt128.e.push_back(e1);
				rt128.e.push_back(e3);
				rt128.calc_arity(nullptr);
				sprawformtree ft127 = std::make_shared<raw_form_tree>(elem::NONE, rt128);
				raw_rule rr129;
				rr129.h.push_back(rt126);
				rr129.set_prft(ft127);
				elem e130;
				e130.type = elem::SYM;
				e130.e = d.get_lexeme("COUNTDOWN4");
				raw_term rt131;
				rt131.neg = false;
				rt131.extype = raw_term::REL;
				rt131.e.push_back(e130);
				rt131.e.push_back(e1);
				rt131.e.push_back(e3);
				rt131.calc_arity(nullptr);
				raw_term rt133;
				rt133.neg = false;
				rt133.extype = raw_term::REL;
				rt133.e.push_back(e125);
				rt133.e.push_back(e1);
				rt133.e.push_back(e3);
				rt133.calc_arity(nullptr);
				sprawformtree ft132 = std::make_shared<raw_form_tree>(elem::NONE, rt133);
				raw_rule rr134;
				rr134.h.push_back(rt131);
				rr134.set_prft(ft132);
				elem e135;
				e135.type = elem::SYM;
				e135.e = d.get_lexeme("COUNTDOWN5");
				raw_term rt136;
				rt136.neg = false;
				rt136.extype = raw_term::REL;
				rt136.e.push_back(e135);
				rt136.e.push_back(e1);
				rt136.e.push_back(e3);
				rt136.calc_arity(nullptr);
				raw_term rt138;
				rt138.neg = false;
				rt138.extype = raw_term::REL;
				rt138.e.push_back(e130);
				rt138.e.push_back(e1);
				rt138.e.push_back(e3);
				rt138.calc_arity(nullptr);
				sprawformtree ft137 = std::make_shared<raw_form_tree>(elem::NONE, rt138);
				raw_rule rr139;
				rr139.h.push_back(rt136);
				rr139.set_prft(ft137);
				elem e140;
				e140.type = elem::SYM;
				e140.e = d.get_lexeme("COUNTDOWN6");
				raw_term rt141;
				rt141.neg = false;
				rt141.extype = raw_term::REL;
				rt141.e.push_back(e140);
				rt141.e.push_back(e1);
				rt141.e.push_back(e3);
				rt141.calc_arity(nullptr);
				raw_term rt143;
				rt143.neg = false;
				rt143.extype = raw_term::REL;
				rt143.e.push_back(e135);
				rt143.e.push_back(e1);
				rt143.e.push_back(e3);
				rt143.calc_arity(nullptr);
				sprawformtree ft142 = std::make_shared<raw_form_tree>(elem::NONE, rt143);
				raw_rule rr144;
				rr144.h.push_back(rt141);
				rr144.set_prft(ft142);
				raw_term rt145;
				rt145.neg = false;
				rt145.extype = raw_term::REL;
				rt145.e.push_back(e47);
				rt145.e.push_back(e1);
				rt145.e.push_back(e3);
				rt145.calc_arity(nullptr);
				raw_term rt148;
				rt148.neg = false;
				rt148.extype = raw_term::REL;
				rt148.e.push_back(e135);
				rt148.e.push_back(e1);
				rt148.e.push_back(e3);
				rt148.calc_arity(nullptr);
				sprawformtree ft147 = std::make_shared<raw_form_tree>(elem::NONE, rt148);
				raw_term rt151;
				rt151.neg = false;
				rt151.extype = raw_term::REL;
				rt151.e.push_back(e140);
				rt151.e.push_back(e1);
				rt151.e.push_back(e3);
				rt151.calc_arity(nullptr);
				sprawformtree ft150 = std::make_shared<raw_form_tree>(elem::NONE, rt151);
				sprawformtree ft149 = std::make_shared<raw_form_tree>(elem::NOT, ft150);
				sprawformtree ft146 = std::make_shared<raw_form_tree>(elem::AND, ft147, ft149);
				raw_rule rr152;
				rr152.h.push_back(rt145);
				rr152.set_prft(ft146);
				elem e153;
				e153.type = elem::SYM;
				e153.e = d.get_lexeme("DOMAIN");
				raw_term rt154;
				rt154.neg = false;
				rt154.extype = raw_term::REL;
				rt154.e.push_back(e153);
				rt154.e.push_back(e1);
				rt154.e.push_back(e62);
				rt154.e.push_back(e3);
				rt154.calc_arity(nullptr);
				elem &e156 = domain_sym;
				elem e157;
				e157.type = elem::VAR;
				e157.e = d.get_lexeme("?w");
				raw_term rt158;
				rt158.neg = false;
				rt158.extype = raw_term::REL;
				rt158.e.push_back(e156);
				rt158.e.push_back(e1);
				rt158.e.push_back(e157);
				rt158.e.push_back(e62);
				rt158.e.push_back(e50);
				rt158.e.push_back(e3);
				rt158.calc_arity(nullptr);
				sprawformtree ft155 = std::make_shared<raw_form_tree>(elem::NONE, rt158);
				raw_rule rr159;
				rr159.h.push_back(rt154);
				rr159.set_prft(ft155);
				elem e160;
				e160.type = elem::SYM;
				e160.e = d.get_lexeme("LIST");
				raw_term rt161;
				rt161.neg = false;
				rt161.extype = raw_term::REL;
				rt161.e.push_back(e160);
				rt161.e.push_back(e1);
				rt161.e.push_back(e2);
				rt161.e.push_back(e3);
				rt161.calc_arity(nullptr);
				raw_term rt163;
				rt163.neg = false;
				rt163.extype = raw_term::REL;
				rt163.e.push_back(e156);
				rt163.e.push_back(e1);
				rt163.e.push_back(e2);
				rt163.e.push_back(e3);
				rt163.calc_arity(nullptr);
				sprawformtree ft162 = std::make_shared<raw_form_tree>(elem::NONE, rt163);
				raw_rule rr164;
				rr164.h.push_back(rt161);
				rr164.set_prft(ft162);
				elem e165;
				e165.type = elem::VAR;
				e165.e = d.get_lexeme("?a");
				raw_term rt166;
				rt166.neg = false;
				rt166.extype = raw_term::REL;
				rt166.e.push_back(e160);
				rt166.e.push_back(e1);
				rt166.e.push_back(e2);
				rt166.e.push_back(e165);
				rt166.e.push_back(e3);
				rt166.calc_arity(nullptr);
				elem e169;
				e169.type = elem::VAR;
				e169.e = d.get_lexeme("?rst");
				raw_term rt170;
				rt170.neg = false;
				rt170.extype = raw_term::REL;
				rt170.e.push_back(e156);
				rt170.e.push_back(e1);
				rt170.e.push_back(e2);
				rt170.e.push_back(e165);
				rt170.e.push_back(e169);
				rt170.e.push_back(e3);
				rt170.calc_arity(nullptr);
				sprawformtree ft168 = std::make_shared<raw_form_tree>(elem::NONE, rt170);
				raw_term rt172;
				rt172.neg = false;
				rt172.extype = raw_term::REL;
				rt172.e.push_back(e160);
				rt172.e.push_back(e1);
				rt172.e.push_back(e169);
				rt172.e.push_back(e3);
				rt172.calc_arity(nullptr);
				sprawformtree ft171 = std::make_shared<raw_form_tree>(elem::NONE, rt172);
				sprawformtree ft167 = std::make_shared<raw_form_tree>(elem::AND, ft168, ft171);
				raw_rule rr173;
				rr173.h.push_back(rt166);
				rr173.set_prft(ft167);
				raw_term rt174;
				rt174.neg = false;
				rt174.extype = raw_term::REL;
				rt174.e.push_back(e160);
				rt174.e.push_back(e1);
				rt174.e.push_back(e2);
				rt174.e.push_back(e165);
				rt174.e.push_back(e42);
				rt174.e.push_back(e3);
				rt174.calc_arity(nullptr);
				raw_term rt177;
				rt177.neg = false;
				rt177.extype = raw_term::REL;
				rt177.e.push_back(e156);
				rt177.e.push_back(e1);
				rt177.e.push_back(e2);
				rt177.e.push_back(e165);
				rt177.e.push_back(e169);
				rt177.e.push_back(e3);
				rt177.calc_arity(nullptr);
				sprawformtree ft176 = std::make_shared<raw_form_tree>(elem::NONE, rt177);
				raw_term rt179;
				rt179.neg = false;
				rt179.extype = raw_term::REL;
				rt179.e.push_back(e160);
				rt179.e.push_back(e1);
				rt179.e.push_back(e169);
				rt179.e.push_back(e42);
				rt179.e.push_back(e3);
				rt179.calc_arity(nullptr);
				sprawformtree ft178 = std::make_shared<raw_form_tree>(elem::NONE, rt179);
				sprawformtree ft175 = std::make_shared<raw_form_tree>(elem::AND, ft176, ft178);
				raw_rule rr180;
				rr180.h.push_back(rt174);
				rr180.set_prft(ft175);
				elem e181;
				e181.type = elem::VAR;
				e181.e = d.get_lexeme("?c");
				raw_term rt182;
				rt182.neg = false;
				rt182.extype = raw_term::REL;
				rt182.e.push_back(e160);
				rt182.e.push_back(e1);
				rt182.e.push_back(e2);
				rt182.e.push_back(e165);
				rt182.e.push_back(e42);
				rt182.e.push_back(e181);
				rt182.e.push_back(e3);
				rt182.calc_arity(nullptr);
				raw_term rt185;
				rt185.neg = false;
				rt185.extype = raw_term::REL;
				rt185.e.push_back(e156);
				rt185.e.push_back(e1);
				rt185.e.push_back(e2);
				rt185.e.push_back(e165);
				rt185.e.push_back(e169);
				rt185.e.push_back(e3);
				rt185.calc_arity(nullptr);
				sprawformtree ft184 = std::make_shared<raw_form_tree>(elem::NONE, rt185);
				raw_term rt187;
				rt187.neg = false;
				rt187.extype = raw_term::REL;
				rt187.e.push_back(e160);
				rt187.e.push_back(e1);
				rt187.e.push_back(e169);
				rt187.e.push_back(e42);
				rt187.e.push_back(e181);
				rt187.e.push_back(e3);
				rt187.calc_arity(nullptr);
				sprawformtree ft186 = std::make_shared<raw_form_tree>(elem::NONE, rt187);
				sprawformtree ft183 = std::make_shared<raw_form_tree>(elem::AND, ft184, ft186);
				raw_rule rr188;
				rr188.h.push_back(rt182);
				rr188.set_prft(ft183);
				elem e189;
				e189.type = elem::VAR;
				e189.e = d.get_lexeme("?d");
				raw_term rt190;
				rt190.neg = false;
				rt190.extype = raw_term::REL;
				rt190.e.push_back(e160);
				rt190.e.push_back(e1);
				rt190.e.push_back(e2);
				rt190.e.push_back(e165);
				rt190.e.push_back(e42);
				rt190.e.push_back(e181);
				rt190.e.push_back(e189);
				rt190.e.push_back(e3);
				rt190.calc_arity(nullptr);
				raw_term rt193;
				rt193.neg = false;
				rt193.extype = raw_term::REL;
				rt193.e.push_back(e156);
				rt193.e.push_back(e1);
				rt193.e.push_back(e2);
				rt193.e.push_back(e165);
				rt193.e.push_back(e169);
				rt193.e.push_back(e3);
				rt193.calc_arity(nullptr);
				sprawformtree ft192 = std::make_shared<raw_form_tree>(elem::NONE, rt193);
				raw_term rt195;
				rt195.neg = false;
				rt195.extype = raw_term::REL;
				rt195.e.push_back(e160);
				rt195.e.push_back(e1);
				rt195.e.push_back(e169);
				rt195.e.push_back(e42);
				rt195.e.push_back(e181);
				rt195.e.push_back(e189);
				rt195.e.push_back(e3);
				rt195.calc_arity(nullptr);
				sprawformtree ft194 = std::make_shared<raw_form_tree>(elem::NONE, rt195);
				sprawformtree ft191 = std::make_shared<raw_form_tree>(elem::AND, ft192, ft194);
				raw_rule rr196;
				rr196.h.push_back(rt190);
				rr196.set_prft(ft191);
				elem e197;
				e197.type = elem::SYM;
				e197.e = d.get_lexeme("DO_RAPPEND0");
				elem e198;
				e198.type = elem::VAR;
				e198.e = d.get_lexeme("?xs");
				elem e199;
				e199.type = elem::VAR;
				e199.e = d.get_lexeme("?ys");
				raw_term rt200;
				rt200.neg = false;
				rt200.extype = raw_term::REL;
				rt200.e.push_back(e197);
				rt200.e.push_back(e1);
				rt200.e.push_back(e198);
				rt200.e.push_back(e199);
				rt200.e.push_back(e198);
				rt200.e.push_back(e199);
				rt200.e.push_back(e3);
				rt200.calc_arity(nullptr);
				elem e203;
				e203.type = elem::SYM;
				e203.e = d.get_lexeme("DO_RAPPEND");
				raw_term rt204;
				rt204.neg = false;
				rt204.extype = raw_term::REL;
				rt204.e.push_back(e203);
				rt204.e.push_back(e1);
				rt204.e.push_back(e198);
				rt204.e.push_back(e199);
				rt204.e.push_back(e3);
				rt204.calc_arity(nullptr);
				sprawformtree ft202 = std::make_shared<raw_form_tree>(elem::NONE, rt204);
				elem e208;
				e208.type = elem::VAR;
				e208.e = d.get_lexeme("?cs");
				sprawformtree ft207 = std::make_shared<raw_form_tree>(elem::VAR, e208);
				elem e210;
				e210.type = elem::SYM;
				e210.e = d.get_lexeme("RAPPEND");
				raw_term rt211;
				rt211.neg = false;
				rt211.extype = raw_term::REL;
				rt211.e.push_back(e210);
				rt211.e.push_back(e1);
				rt211.e.push_back(e208);
				rt211.e.push_back(e198);
				rt211.e.push_back(e199);
				rt211.e.push_back(e3);
				rt211.calc_arity(nullptr);
				sprawformtree ft209 = std::make_shared<raw_form_tree>(elem::NONE, rt211);
				sprawformtree ft206 = std::make_shared<raw_form_tree>(elem::EXISTS, ft207, ft209);
				sprawformtree ft205 = std::make_shared<raw_form_tree>(elem::NOT, ft206);
				sprawformtree ft201 = std::make_shared<raw_form_tree>(elem::AND, ft202, ft205);
				raw_rule rr212;
				rr212.h.push_back(rt200);
				rr212.set_prft(ft201);
				elem e213;
				e213.type = elem::VAR;
				e213.e = d.get_lexeme("?oxs");
				elem e214;
				e214.type = elem::VAR;
				e214.e = d.get_lexeme("?oys");
				elem e215;
				e215.type = elem::VAR;
				e215.e = d.get_lexeme("?xs_tl");
				raw_term rt216;
				rt216.neg = false;
				rt216.extype = raw_term::REL;
				rt216.e.push_back(e197);
				rt216.e.push_back(e1);
				rt216.e.push_back(e213);
				rt216.e.push_back(e214);
				rt216.e.push_back(e215);
				rt216.e.push_back(e199);
				rt216.e.push_back(e3);
				rt216.calc_arity(nullptr);
				elem e221;
				e221.type = elem::VAR;
				e221.e = d.get_lexeme("?ys_tl");
				raw_term rt222;
				rt222.neg = false;
				rt222.extype = raw_term::REL;
				rt222.e.push_back(e197);
				rt222.e.push_back(e1);
				rt222.e.push_back(e213);
				rt222.e.push_back(e214);
				rt222.e.push_back(e198);
				rt222.e.push_back(e221);
				rt222.e.push_back(e3);
				rt222.calc_arity(nullptr);
				sprawformtree ft220 = std::make_shared<raw_form_tree>(elem::NONE, rt222);
				elem e224;
				e224.type = elem::VAR;
				e224.e = d.get_lexeme("?xs_hd");
				raw_term rt225;
				rt225.neg = false;
				rt225.extype = raw_term::REL;
				rt225.e.push_back(e156);
				rt225.e.push_back(e1);
				rt225.e.push_back(e198);
				rt225.e.push_back(e224);
				rt225.e.push_back(e215);
				rt225.e.push_back(e3);
				rt225.calc_arity(nullptr);
				sprawformtree ft223 = std::make_shared<raw_form_tree>(elem::NONE, rt225);
				sprawformtree ft219 = std::make_shared<raw_form_tree>(elem::AND, ft220, ft223);
				raw_term rt227;
				rt227.neg = false;
				rt227.extype = raw_term::REL;
				rt227.e.push_back(e156);
				rt227.e.push_back(e1);
				rt227.e.push_back(e199);
				rt227.e.push_back(e224);
				rt227.e.push_back(e221);
				rt227.e.push_back(e3);
				rt227.calc_arity(nullptr);
				sprawformtree ft226 = std::make_shared<raw_form_tree>(elem::NONE, rt227);
				sprawformtree ft218 = std::make_shared<raw_form_tree>(elem::AND, ft219, ft226);
				sprawformtree ft230 = std::make_shared<raw_form_tree>(elem::VAR, e208);
				raw_term rt232;
				rt232.neg = false;
				rt232.extype = raw_term::REL;
				rt232.e.push_back(e210);
				rt232.e.push_back(e1);
				rt232.e.push_back(e208);
				rt232.e.push_back(e213);
				rt232.e.push_back(e214);
				rt232.e.push_back(e3);
				rt232.calc_arity(nullptr);
				sprawformtree ft231 = std::make_shared<raw_form_tree>(elem::NONE, rt232);
				sprawformtree ft229 = std::make_shared<raw_form_tree>(elem::EXISTS, ft230, ft231);
				sprawformtree ft228 = std::make_shared<raw_form_tree>(elem::NOT, ft229);
				sprawformtree ft217 = std::make_shared<raw_form_tree>(elem::AND, ft218, ft228);
				raw_rule rr233;
				rr233.h.push_back(rt216);
				rr233.set_prft(ft217);
				elem e234;
				e234.type = elem::VAR;
				e234.e = d.get_lexeme("?zs");
				raw_term rt235;
				rt235.neg = false;
				rt235.extype = raw_term::REL;
				rt235.e.push_back(e210);
				rt235.e.push_back(e1);
				rt235.e.push_back(e234);
				rt235.e.push_back(e198);
				rt235.e.push_back(e199);
				rt235.e.push_back(e3);
				rt235.calc_arity(nullptr);
				elem e239;
				e239.type = elem::VAR;
				e239.e = d.get_lexeme("?as");
				raw_term rt240;
				rt240.neg = false;
				rt240.extype = raw_term::REL;
				rt240.e.push_back(e197);
				rt240.e.push_back(e1);
				rt240.e.push_back(e198);
				rt240.e.push_back(e199);
				rt240.e.push_back(e239);
				rt240.e.push_back(e234);
				rt240.e.push_back(e3);
				rt240.calc_arity(nullptr);
				sprawformtree ft238 = std::make_shared<raw_form_tree>(elem::NONE, rt240);
				raw_term rt242;
				rt242.neg = false;
				rt242.extype = raw_term::REL;
				rt242.e.push_back(e156);
				rt242.e.push_back(e1);
				rt242.e.push_back(e239);
				rt242.e.push_back(e3);
				rt242.calc_arity(nullptr);
				sprawformtree ft241 = std::make_shared<raw_form_tree>(elem::NONE, rt242);
				sprawformtree ft237 = std::make_shared<raw_form_tree>(elem::AND, ft238, ft241);
				sprawformtree ft245 = std::make_shared<raw_form_tree>(elem::VAR, e208);
				raw_term rt247;
				rt247.neg = false;
				rt247.extype = raw_term::REL;
				rt247.e.push_back(e210);
				rt247.e.push_back(e1);
				rt247.e.push_back(e208);
				rt247.e.push_back(e198);
				rt247.e.push_back(e199);
				rt247.e.push_back(e3);
				rt247.calc_arity(nullptr);
				sprawformtree ft246 = std::make_shared<raw_form_tree>(elem::NONE, rt247);
				sprawformtree ft244 = std::make_shared<raw_form_tree>(elem::EXISTS, ft245, ft246);
				sprawformtree ft243 = std::make_shared<raw_form_tree>(elem::NOT, ft244);
				sprawformtree ft236 = std::make_shared<raw_form_tree>(elem::AND, ft237, ft243);
				raw_rule rr248;
				rr248.h.push_back(rt235);
				rr248.set_prft(ft236);
				raw_term rt249;
				rt249.neg = true;
				rt249.extype = raw_term::REL;
				rt249.e.push_back(e197);
				rt249.e.push_back(e1);
				rt249.e.push_back(e213);
				rt249.e.push_back(e214);
				rt249.e.push_back(e198);
				rt249.e.push_back(e199);
				rt249.e.push_back(e3);
				rt249.calc_arity(nullptr);
				raw_term rt251;
				rt251.neg = false;
				rt251.extype = raw_term::REL;
				rt251.e.push_back(e210);
				rt251.e.push_back(e1);
				rt251.e.push_back(e208);
				rt251.e.push_back(e213);
				rt251.e.push_back(e214);
				rt251.e.push_back(e3);
				rt251.calc_arity(nullptr);
				sprawformtree ft250 = std::make_shared<raw_form_tree>(elem::NONE, rt251);
				raw_rule rr252;
				rr252.h.push_back(rt249);
				rr252.set_prft(ft250);
				elem e253;
				e253.type = elem::SYM;
				e253.e = d.get_lexeme("DO_REVERSE");
				elem e254;
				e254.type = elem::VAR;
				e254.e = d.get_lexeme("?bs");
				raw_term rt255;
				rt255.neg = false;
				rt255.extype = raw_term::REL;
				rt255.e.push_back(e253);
				rt255.e.push_back(e1);
				rt255.e.push_back(e254);
				rt255.e.push_back(e239);
				rt255.e.push_back(e254);
				rt255.e.push_back(e3);
				rt255.calc_arity(nullptr);
				raw_term rt259;
				rt259.neg = false;
				rt259.extype = raw_term::REL;
				rt259.e.push_back(e253);
				rt259.e.push_back(e1);
				rt259.e.push_back(e254);
				rt259.e.push_back(e3);
				rt259.calc_arity(nullptr);
				sprawformtree ft258 = std::make_shared<raw_form_tree>(elem::NONE, rt259);
				raw_term rt261;
				rt261.neg = false;
				rt261.extype = raw_term::REL;
				rt261.e.push_back(e156);
				rt261.e.push_back(e1);
				rt261.e.push_back(e239);
				rt261.e.push_back(e3);
				rt261.calc_arity(nullptr);
				sprawformtree ft260 = std::make_shared<raw_form_tree>(elem::NONE, rt261);
				sprawformtree ft257 = std::make_shared<raw_form_tree>(elem::AND, ft258, ft260);
				sprawformtree ft264 = std::make_shared<raw_form_tree>(elem::VAR, e165);
				elem e266;
				e266.type = elem::SYM;
				e266.e = d.get_lexeme("REVERSE");
				raw_term rt267;
				rt267.neg = false;
				rt267.extype = raw_term::REL;
				rt267.e.push_back(e266);
				rt267.e.push_back(e1);
				rt267.e.push_back(e254);
				rt267.e.push_back(e165);
				rt267.e.push_back(e3);
				rt267.calc_arity(nullptr);
				sprawformtree ft265 = std::make_shared<raw_form_tree>(elem::NONE, rt267);
				sprawformtree ft263 = std::make_shared<raw_form_tree>(elem::EXISTS, ft264, ft265);
				sprawformtree ft262 = std::make_shared<raw_form_tree>(elem::NOT, ft263);
				sprawformtree ft256 = std::make_shared<raw_form_tree>(elem::AND, ft257, ft262);
				raw_rule rr268;
				rr268.h.push_back(rt255);
				rr268.set_prft(ft256);
				elem e269;
				e269.type = elem::VAR;
				e269.e = d.get_lexeme("?obs");
				raw_term rt270;
				rt270.neg = false;
				rt270.extype = raw_term::REL;
				rt270.e.push_back(e253);
				rt270.e.push_back(e1);
				rt270.e.push_back(e269);
				rt270.e.push_back(e239);
				rt270.e.push_back(e254);
				rt270.e.push_back(e3);
				rt270.calc_arity(nullptr);
				elem e275;
				e275.type = elem::VAR;
				e275.e = d.get_lexeme("?as_hd");
				elem e276;
				e276.type = elem::VAR;
				e276.e = d.get_lexeme("?as_tl");
				raw_term rt277;
				rt277.neg = false;
				rt277.extype = raw_term::REL;
				rt277.e.push_back(e156);
				rt277.e.push_back(e1);
				rt277.e.push_back(e239);
				rt277.e.push_back(e275);
				rt277.e.push_back(e276);
				rt277.e.push_back(e3);
				rt277.calc_arity(nullptr);
				sprawformtree ft274 = std::make_shared<raw_form_tree>(elem::NONE, rt277);
				elem e279;
				e279.type = elem::VAR;
				e279.e = d.get_lexeme("?nbs");
				raw_term rt280;
				rt280.neg = false;
				rt280.extype = raw_term::REL;
				rt280.e.push_back(e156);
				rt280.e.push_back(e1);
				rt280.e.push_back(e279);
				rt280.e.push_back(e275);
				rt280.e.push_back(e254);
				rt280.e.push_back(e3);
				rt280.calc_arity(nullptr);
				sprawformtree ft278 = std::make_shared<raw_form_tree>(elem::NONE, rt280);
				sprawformtree ft273 = std::make_shared<raw_form_tree>(elem::AND, ft274, ft278);
				raw_term rt282;
				rt282.neg = false;
				rt282.extype = raw_term::REL;
				rt282.e.push_back(e253);
				rt282.e.push_back(e1);
				rt282.e.push_back(e269);
				rt282.e.push_back(e276);
				rt282.e.push_back(e279);
				rt282.e.push_back(e3);
				rt282.calc_arity(nullptr);
				sprawformtree ft281 = std::make_shared<raw_form_tree>(elem::NONE, rt282);
				sprawformtree ft272 = std::make_shared<raw_form_tree>(elem::AND, ft273, ft281);
				sprawformtree ft285 = std::make_shared<raw_form_tree>(elem::VAR, e165);
				raw_term rt287;
				rt287.neg = false;
				rt287.extype = raw_term::REL;
				rt287.e.push_back(e266);
				rt287.e.push_back(e1);
				rt287.e.push_back(e269);
				rt287.e.push_back(e165);
				rt287.e.push_back(e3);
				rt287.calc_arity(nullptr);
				sprawformtree ft286 = std::make_shared<raw_form_tree>(elem::NONE, rt287);
				sprawformtree ft284 = std::make_shared<raw_form_tree>(elem::EXISTS, ft285, ft286);
				sprawformtree ft283 = std::make_shared<raw_form_tree>(elem::NOT, ft284);
				sprawformtree ft271 = std::make_shared<raw_form_tree>(elem::AND, ft272, ft283);
				raw_rule rr288;
				rr288.h.push_back(rt270);
				rr288.set_prft(ft271);
				raw_term rt289;
				rt289.neg = false;
				rt289.extype = raw_term::REL;
				rt289.e.push_back(e266);
				rt289.e.push_back(e1);
				rt289.e.push_back(e269);
				rt289.e.push_back(e239);
				rt289.e.push_back(e3);
				rt289.calc_arity(nullptr);
				raw_term rt293;
				rt293.neg = false;
				rt293.extype = raw_term::REL;
				rt293.e.push_back(e253);
				rt293.e.push_back(e1);
				rt293.e.push_back(e269);
				rt293.e.push_back(e239);
				rt293.e.push_back(e254);
				rt293.e.push_back(e3);
				rt293.calc_arity(nullptr);
				sprawformtree ft292 = std::make_shared<raw_form_tree>(elem::NONE, rt293);
				raw_term rt295;
				rt295.neg = false;
				rt295.extype = raw_term::REL;
				rt295.e.push_back(e156);
				rt295.e.push_back(e1);
				rt295.e.push_back(e254);
				rt295.e.push_back(e3);
				rt295.calc_arity(nullptr);
				sprawformtree ft294 = std::make_shared<raw_form_tree>(elem::NONE, rt295);
				sprawformtree ft291 = std::make_shared<raw_form_tree>(elem::AND, ft292, ft294);
				sprawformtree ft298 = std::make_shared<raw_form_tree>(elem::VAR, e165);
				raw_term rt300;
				rt300.neg = false;
				rt300.extype = raw_term::REL;
				rt300.e.push_back(e266);
				rt300.e.push_back(e1);
				rt300.e.push_back(e269);
				rt300.e.push_back(e165);
				rt300.e.push_back(e3);
				rt300.calc_arity(nullptr);
				sprawformtree ft299 = std::make_shared<raw_form_tree>(elem::NONE, rt300);
				sprawformtree ft297 = std::make_shared<raw_form_tree>(elem::EXISTS, ft298, ft299);
				sprawformtree ft296 = std::make_shared<raw_form_tree>(elem::NOT, ft297);
				sprawformtree ft290 = std::make_shared<raw_form_tree>(elem::AND, ft291, ft296);
				raw_rule rr301;
				rr301.h.push_back(rt289);
				rr301.set_prft(ft290);
				raw_term rt302;
				rt302.neg = true;
				rt302.extype = raw_term::REL;
				rt302.e.push_back(e253);
				rt302.e.push_back(e1);
				rt302.e.push_back(e269);
				rt302.e.push_back(e239);
				rt302.e.push_back(e254);
				rt302.e.push_back(e3);
				rt302.calc_arity(nullptr);
				raw_term rt304;
				rt304.neg = false;
				rt304.extype = raw_term::REL;
				rt304.e.push_back(e266);
				rt304.e.push_back(e1);
				rt304.e.push_back(e269);
				rt304.e.push_back(e208);
				rt304.e.push_back(e3);
				rt304.calc_arity(nullptr);
				sprawformtree ft303 = std::make_shared<raw_form_tree>(elem::NONE, rt304);
				raw_rule rr305;
				rr305.h.push_back(rt302);
				rr305.set_prft(ft303);
				elem e306;
				e306.type = elem::SYM;
				e306.e = d.get_lexeme("ASSOC0");
				raw_term rt307;
				rt307.neg = false;
				rt307.extype = raw_term::REL;
				rt307.e.push_back(e306);
				rt307.e.push_back(e1);
				rt307.e.push_back(e198);
				rt307.e.push_back(e199);
				rt307.e.push_back(e198);
				rt307.e.push_back(e199);
				rt307.e.push_back(e62);
				rt307.e.push_back(e3);
				rt307.calc_arity(nullptr);
				elem e311;
				e311.type = elem::SYM;
				e311.e = d.get_lexeme("ASSOC");
				raw_term rt312;
				rt312.neg = false;
				rt312.extype = raw_term::REL;
				rt312.e.push_back(e311);
				rt312.e.push_back(e1);
				rt312.e.push_back(e198);
				rt312.e.push_back(e199);
				rt312.e.push_back(e62);
				rt312.e.push_back(e3);
				rt312.calc_arity(nullptr);
				sprawformtree ft310 = std::make_shared<raw_form_tree>(elem::NONE, rt312);
				sprawformtree ft315 = std::make_shared<raw_form_tree>(elem::VAR, e50);
				raw_term rt317;
				rt317.neg = false;
				rt317.extype = raw_term::REL;
				rt317.e.push_back(e311);
				rt317.e.push_back(e1);
				rt317.e.push_back(e198);
				rt317.e.push_back(e199);
				rt317.e.push_back(e62);
				rt317.e.push_back(e50);
				rt317.e.push_back(e3);
				rt317.calc_arity(nullptr);
				sprawformtree ft316 = std::make_shared<raw_form_tree>(elem::NONE, rt317);
				sprawformtree ft314 = std::make_shared<raw_form_tree>(elem::EXISTS, ft315, ft316);
				sprawformtree ft313 = std::make_shared<raw_form_tree>(elem::NOT, ft314);
				sprawformtree ft309 = std::make_shared<raw_form_tree>(elem::AND, ft310, ft313);
				elem e320;
				e320.type = elem::SYM;
				e320.e = d.get_lexeme("NO_ASSOC");
				raw_term rt321;
				rt321.neg = false;
				rt321.extype = raw_term::REL;
				rt321.e.push_back(e320);
				rt321.e.push_back(e1);
				rt321.e.push_back(e198);
				rt321.e.push_back(e199);
				rt321.e.push_back(e62);
				rt321.e.push_back(e3);
				rt321.calc_arity(nullptr);
				sprawformtree ft319 = std::make_shared<raw_form_tree>(elem::NONE, rt321);
				sprawformtree ft318 = std::make_shared<raw_form_tree>(elem::NOT, ft319);
				sprawformtree ft308 = std::make_shared<raw_form_tree>(elem::AND, ft309, ft318);
				raw_rule rr322;
				rr322.h.push_back(rt307);
				rr322.set_prft(ft308);
				elem e323;
				e323.type = elem::VAR;
				e323.e = d.get_lexeme("?yn");
				raw_term rt324;
				rt324.neg = false;
				rt324.extype = raw_term::REL;
				rt324.e.push_back(e306);
				rt324.e.push_back(e1);
				rt324.e.push_back(e213);
				rt324.e.push_back(e214);
				rt324.e.push_back(e215);
				rt324.e.push_back(e221);
				rt324.e.push_back(e62);
				rt324.e.push_back(e323);
				rt324.e.push_back(e3);
				rt324.calc_arity(nullptr);
				raw_term rt330;
				rt330.neg = false;
				rt330.extype = raw_term::REL;
				rt330.e.push_back(e156);
				rt330.e.push_back(e1);
				rt330.e.push_back(e198);
				rt330.e.push_back(e62);
				rt330.e.push_back(e215);
				rt330.e.push_back(e3);
				rt330.calc_arity(nullptr);
				sprawformtree ft329 = std::make_shared<raw_form_tree>(elem::NONE, rt330);
				raw_term rt332;
				rt332.neg = false;
				rt332.extype = raw_term::REL;
				rt332.e.push_back(e156);
				rt332.e.push_back(e1);
				rt332.e.push_back(e199);
				rt332.e.push_back(e323);
				rt332.e.push_back(e221);
				rt332.e.push_back(e3);
				rt332.calc_arity(nullptr);
				sprawformtree ft331 = std::make_shared<raw_form_tree>(elem::NONE, rt332);
				sprawformtree ft328 = std::make_shared<raw_form_tree>(elem::AND, ft329, ft331);
				raw_term rt334;
				rt334.neg = false;
				rt334.extype = raw_term::REL;
				rt334.e.push_back(e306);
				rt334.e.push_back(e1);
				rt334.e.push_back(e213);
				rt334.e.push_back(e214);
				rt334.e.push_back(e198);
				rt334.e.push_back(e199);
				rt334.e.push_back(e62);
				rt334.e.push_back(e3);
				rt334.calc_arity(nullptr);
				sprawformtree ft333 = std::make_shared<raw_form_tree>(elem::NONE, rt334);
				sprawformtree ft327 = std::make_shared<raw_form_tree>(elem::AND, ft328, ft333);
				sprawformtree ft337 = std::make_shared<raw_form_tree>(elem::VAR, e50);
				raw_term rt339;
				rt339.neg = false;
				rt339.extype = raw_term::REL;
				rt339.e.push_back(e311);
				rt339.e.push_back(e1);
				rt339.e.push_back(e213);
				rt339.e.push_back(e214);
				rt339.e.push_back(e62);
				rt339.e.push_back(e50);
				rt339.e.push_back(e3);
				rt339.calc_arity(nullptr);
				sprawformtree ft338 = std::make_shared<raw_form_tree>(elem::NONE, rt339);
				sprawformtree ft336 = std::make_shared<raw_form_tree>(elem::EXISTS, ft337, ft338);
				sprawformtree ft335 = std::make_shared<raw_form_tree>(elem::NOT, ft336);
				sprawformtree ft326 = std::make_shared<raw_form_tree>(elem::AND, ft327, ft335);
				raw_term rt342;
				rt342.neg = false;
				rt342.extype = raw_term::REL;
				rt342.e.push_back(e320);
				rt342.e.push_back(e1);
				rt342.e.push_back(e213);
				rt342.e.push_back(e214);
				rt342.e.push_back(e62);
				rt342.e.push_back(e3);
				rt342.calc_arity(nullptr);
				sprawformtree ft341 = std::make_shared<raw_form_tree>(elem::NONE, rt342);
				sprawformtree ft340 = std::make_shared<raw_form_tree>(elem::NOT, ft341);
				sprawformtree ft325 = std::make_shared<raw_form_tree>(elem::AND, ft326, ft340);
				raw_rule rr343;
				rr343.h.push_back(rt324);
				rr343.set_prft(ft325);
				raw_term rt344;
				rt344.neg = false;
				rt344.extype = raw_term::REL;
				rt344.e.push_back(e320);
				rt344.e.push_back(e1);
				rt344.e.push_back(e213);
				rt344.e.push_back(e214);
				rt344.e.push_back(e62);
				rt344.e.push_back(e3);
				rt344.calc_arity(nullptr);
				raw_term rt350;
				rt350.neg = false;
				rt350.extype = raw_term::REL;
				rt350.e.push_back(e156);
				rt350.e.push_back(e1);
				rt350.e.push_back(e198);
				rt350.e.push_back(e62);
				rt350.e.push_back(e215);
				rt350.e.push_back(e3);
				rt350.calc_arity(nullptr);
				sprawformtree ft349 = std::make_shared<raw_form_tree>(elem::NONE, rt350);
				raw_term rt352;
				rt352.neg = false;
				rt352.extype = raw_term::REL;
				rt352.e.push_back(e156);
				rt352.e.push_back(e1);
				rt352.e.push_back(e199);
				rt352.e.push_back(e323);
				rt352.e.push_back(e221);
				rt352.e.push_back(e3);
				rt352.calc_arity(nullptr);
				sprawformtree ft351 = std::make_shared<raw_form_tree>(elem::NONE, rt352);
				sprawformtree ft348 = std::make_shared<raw_form_tree>(elem::AND, ft349, ft351);
				raw_term rt354;
				rt354.neg = false;
				rt354.extype = raw_term::REL;
				rt354.e.push_back(e306);
				rt354.e.push_back(e1);
				rt354.e.push_back(e213);
				rt354.e.push_back(e214);
				rt354.e.push_back(e198);
				rt354.e.push_back(e199);
				rt354.e.push_back(e62);
				rt354.e.push_back(e50);
				rt354.e.push_back(e3);
				rt354.calc_arity(nullptr);
				sprawformtree ft353 = std::make_shared<raw_form_tree>(elem::NONE, rt354);
				sprawformtree ft347 = std::make_shared<raw_form_tree>(elem::AND, ft348, ft353);
				sprawformtree ft357 = std::make_shared<raw_form_tree>(elem::VAR, e50);
				raw_term rt359;
				rt359.neg = false;
				rt359.extype = raw_term::REL;
				rt359.e.push_back(e311);
				rt359.e.push_back(e1);
				rt359.e.push_back(e213);
				rt359.e.push_back(e214);
				rt359.e.push_back(e62);
				rt359.e.push_back(e50);
				rt359.e.push_back(e3);
				rt359.calc_arity(nullptr);
				sprawformtree ft358 = std::make_shared<raw_form_tree>(elem::NONE, rt359);
				sprawformtree ft356 = std::make_shared<raw_form_tree>(elem::EXISTS, ft357, ft358);
				sprawformtree ft355 = std::make_shared<raw_form_tree>(elem::NOT, ft356);
				sprawformtree ft346 = std::make_shared<raw_form_tree>(elem::AND, ft347, ft355);
				raw_term rt362;
				rt362.neg = false;
				rt362.extype = raw_term::REL;
				rt362.e.push_back(e320);
				rt362.e.push_back(e1);
				rt362.e.push_back(e213);
				rt362.e.push_back(e214);
				rt362.e.push_back(e62);
				rt362.e.push_back(e3);
				rt362.calc_arity(nullptr);
				sprawformtree ft361 = std::make_shared<raw_form_tree>(elem::NONE, rt362);
				sprawformtree ft360 = std::make_shared<raw_form_tree>(elem::NOT, ft361);
				sprawformtree ft345 = std::make_shared<raw_form_tree>(elem::AND, ft346, ft360);
				raw_rule rr363;
				rr363.h.push_back(rt344);
				rr363.set_prft(ft345);
				raw_term rt364;
				rt364.neg = false;
				rt364.extype = raw_term::REL;
				rt364.e.push_back(e306);
				rt364.e.push_back(e1);
				rt364.e.push_back(e213);
				rt364.e.push_back(e214);
				rt364.e.push_back(e215);
				rt364.e.push_back(e221);
				rt364.e.push_back(e62);
				rt364.e.push_back(e3);
				rt364.calc_arity(nullptr);
				elem e371;
				e371.type = elem::VAR;
				e371.e = d.get_lexeme("?xn");
				raw_term rt372;
				rt372.neg = false;
				rt372.extype = raw_term::REL;
				rt372.e.push_back(e156);
				rt372.e.push_back(e1);
				rt372.e.push_back(e198);
				rt372.e.push_back(e371);
				rt372.e.push_back(e215);
				rt372.e.push_back(e3);
				rt372.calc_arity(nullptr);
				sprawformtree ft370 = std::make_shared<raw_form_tree>(elem::NONE, rt372);
				raw_term rt374;
				rt374.neg = false;
				rt374.extype = raw_term::REL;
				rt374.e.push_back(e156);
				rt374.e.push_back(e1);
				rt374.e.push_back(e199);
				rt374.e.push_back(e323);
				rt374.e.push_back(e221);
				rt374.e.push_back(e3);
				rt374.calc_arity(nullptr);
				sprawformtree ft373 = std::make_shared<raw_form_tree>(elem::NONE, rt374);
				sprawformtree ft369 = std::make_shared<raw_form_tree>(elem::AND, ft370, ft373);
				raw_term rt376;
				rt376.neg = false;
				rt376.extype = raw_term::REL;
				rt376.e.push_back(e306);
				rt376.e.push_back(e1);
				rt376.e.push_back(e213);
				rt376.e.push_back(e214);
				rt376.e.push_back(e198);
				rt376.e.push_back(e199);
				rt376.e.push_back(e62);
				rt376.e.push_back(e3);
				rt376.calc_arity(nullptr);
				sprawformtree ft375 = std::make_shared<raw_form_tree>(elem::NONE, rt376);
				sprawformtree ft368 = std::make_shared<raw_form_tree>(elem::AND, ft369, ft375);
				raw_term rt379;
				rt379.neg = false;
				rt379.extype = raw_term::EQ;
				rt379.e.push_back(e371);
				rt379.e.push_back(e112);
				rt379.e.push_back(e62);
				rt379.calc_arity(nullptr);
				sprawformtree ft378 = std::make_shared<raw_form_tree>(elem::NONE, rt379);
				sprawformtree ft377 = std::make_shared<raw_form_tree>(elem::NOT, ft378);
				sprawformtree ft367 = std::make_shared<raw_form_tree>(elem::AND, ft368, ft377);
				sprawformtree ft382 = std::make_shared<raw_form_tree>(elem::VAR, e50);
				raw_term rt384;
				rt384.neg = false;
				rt384.extype = raw_term::REL;
				rt384.e.push_back(e311);
				rt384.e.push_back(e1);
				rt384.e.push_back(e213);
				rt384.e.push_back(e214);
				rt384.e.push_back(e62);
				rt384.e.push_back(e50);
				rt384.e.push_back(e3);
				rt384.calc_arity(nullptr);
				sprawformtree ft383 = std::make_shared<raw_form_tree>(elem::NONE, rt384);
				sprawformtree ft381 = std::make_shared<raw_form_tree>(elem::EXISTS, ft382, ft383);
				sprawformtree ft380 = std::make_shared<raw_form_tree>(elem::NOT, ft381);
				sprawformtree ft366 = std::make_shared<raw_form_tree>(elem::AND, ft367, ft380);
				raw_term rt387;
				rt387.neg = false;
				rt387.extype = raw_term::REL;
				rt387.e.push_back(e320);
				rt387.e.push_back(e1);
				rt387.e.push_back(e213);
				rt387.e.push_back(e214);
				rt387.e.push_back(e62);
				rt387.e.push_back(e3);
				rt387.calc_arity(nullptr);
				sprawformtree ft386 = std::make_shared<raw_form_tree>(elem::NONE, rt387);
				sprawformtree ft385 = std::make_shared<raw_form_tree>(elem::NOT, ft386);
				sprawformtree ft365 = std::make_shared<raw_form_tree>(elem::AND, ft366, ft385);
				raw_rule rr388;
				rr388.h.push_back(rt364);
				rr388.set_prft(ft365);
				raw_term rt389;
				rt389.neg = false;
				rt389.extype = raw_term::REL;
				rt389.e.push_back(e306);
				rt389.e.push_back(e1);
				rt389.e.push_back(e213);
				rt389.e.push_back(e214);
				rt389.e.push_back(e215);
				rt389.e.push_back(e221);
				rt389.e.push_back(e62);
				rt389.e.push_back(e50);
				rt389.e.push_back(e3);
				rt389.calc_arity(nullptr);
				raw_term rt396;
				rt396.neg = false;
				rt396.extype = raw_term::REL;
				rt396.e.push_back(e156);
				rt396.e.push_back(e1);
				rt396.e.push_back(e198);
				rt396.e.push_back(e371);
				rt396.e.push_back(e215);
				rt396.e.push_back(e3);
				rt396.calc_arity(nullptr);
				sprawformtree ft395 = std::make_shared<raw_form_tree>(elem::NONE, rt396);
				raw_term rt398;
				rt398.neg = false;
				rt398.extype = raw_term::REL;
				rt398.e.push_back(e156);
				rt398.e.push_back(e1);
				rt398.e.push_back(e199);
				rt398.e.push_back(e323);
				rt398.e.push_back(e221);
				rt398.e.push_back(e3);
				rt398.calc_arity(nullptr);
				sprawformtree ft397 = std::make_shared<raw_form_tree>(elem::NONE, rt398);
				sprawformtree ft394 = std::make_shared<raw_form_tree>(elem::AND, ft395, ft397);
				raw_term rt400;
				rt400.neg = false;
				rt400.extype = raw_term::REL;
				rt400.e.push_back(e306);
				rt400.e.push_back(e1);
				rt400.e.push_back(e213);
				rt400.e.push_back(e214);
				rt400.e.push_back(e198);
				rt400.e.push_back(e199);
				rt400.e.push_back(e62);
				rt400.e.push_back(e50);
				rt400.e.push_back(e3);
				rt400.calc_arity(nullptr);
				sprawformtree ft399 = std::make_shared<raw_form_tree>(elem::NONE, rt400);
				sprawformtree ft393 = std::make_shared<raw_form_tree>(elem::AND, ft394, ft399);
				raw_term rt403;
				rt403.neg = false;
				rt403.extype = raw_term::EQ;
				rt403.e.push_back(e371);
				rt403.e.push_back(e112);
				rt403.e.push_back(e62);
				rt403.calc_arity(nullptr);
				sprawformtree ft402 = std::make_shared<raw_form_tree>(elem::NONE, rt403);
				sprawformtree ft401 = std::make_shared<raw_form_tree>(elem::NOT, ft402);
				sprawformtree ft392 = std::make_shared<raw_form_tree>(elem::AND, ft393, ft401);
				sprawformtree ft406 = std::make_shared<raw_form_tree>(elem::VAR, e50);
				raw_term rt408;
				rt408.neg = false;
				rt408.extype = raw_term::REL;
				rt408.e.push_back(e311);
				rt408.e.push_back(e1);
				rt408.e.push_back(e213);
				rt408.e.push_back(e214);
				rt408.e.push_back(e62);
				rt408.e.push_back(e50);
				rt408.e.push_back(e3);
				rt408.calc_arity(nullptr);
				sprawformtree ft407 = std::make_shared<raw_form_tree>(elem::NONE, rt408);
				sprawformtree ft405 = std::make_shared<raw_form_tree>(elem::EXISTS, ft406, ft407);
				sprawformtree ft404 = std::make_shared<raw_form_tree>(elem::NOT, ft405);
				sprawformtree ft391 = std::make_shared<raw_form_tree>(elem::AND, ft392, ft404);
				raw_term rt411;
				rt411.neg = false;
				rt411.extype = raw_term::REL;
				rt411.e.push_back(e320);
				rt411.e.push_back(e1);
				rt411.e.push_back(e213);
				rt411.e.push_back(e214);
				rt411.e.push_back(e62);
				rt411.e.push_back(e3);
				rt411.calc_arity(nullptr);
				sprawformtree ft410 = std::make_shared<raw_form_tree>(elem::NONE, rt411);
				sprawformtree ft409 = std::make_shared<raw_form_tree>(elem::NOT, ft410);
				sprawformtree ft390 = std::make_shared<raw_form_tree>(elem::AND, ft391, ft409);
				raw_rule rr412;
				rr412.h.push_back(rt389);
				rr412.set_prft(ft390);
				raw_term rt413;
				rt413.neg = false;
				rt413.extype = raw_term::REL;
				rt413.e.push_back(e311);
				rt413.e.push_back(e1);
				rt413.e.push_back(e213);
				rt413.e.push_back(e214);
				rt413.e.push_back(e62);
				rt413.e.push_back(e50);
				rt413.e.push_back(e3);
				rt413.calc_arity(nullptr);
				raw_term rt419;
				rt419.neg = false;
				rt419.extype = raw_term::REL;
				rt419.e.push_back(e306);
				rt419.e.push_back(e1);
				rt419.e.push_back(e213);
				rt419.e.push_back(e214);
				rt419.e.push_back(e198);
				rt419.e.push_back(e199);
				rt419.e.push_back(e62);
				rt419.e.push_back(e50);
				rt419.e.push_back(e3);
				rt419.calc_arity(nullptr);
				sprawformtree ft418 = std::make_shared<raw_form_tree>(elem::NONE, rt419);
				raw_term rt421;
				rt421.neg = false;
				rt421.extype = raw_term::REL;
				rt421.e.push_back(e156);
				rt421.e.push_back(e1);
				rt421.e.push_back(e198);
				rt421.e.push_back(e3);
				rt421.calc_arity(nullptr);
				sprawformtree ft420 = std::make_shared<raw_form_tree>(elem::NONE, rt421);
				sprawformtree ft417 = std::make_shared<raw_form_tree>(elem::AND, ft418, ft420);
				raw_term rt423;
				rt423.neg = false;
				rt423.extype = raw_term::REL;
				rt423.e.push_back(e156);
				rt423.e.push_back(e1);
				rt423.e.push_back(e199);
				rt423.e.push_back(e3);
				rt423.calc_arity(nullptr);
				sprawformtree ft422 = std::make_shared<raw_form_tree>(elem::NONE, rt423);
				sprawformtree ft416 = std::make_shared<raw_form_tree>(elem::AND, ft417, ft422);
				sprawformtree ft426 = std::make_shared<raw_form_tree>(elem::VAR, e50);
				raw_term rt428;
				rt428.neg = false;
				rt428.extype = raw_term::REL;
				rt428.e.push_back(e311);
				rt428.e.push_back(e1);
				rt428.e.push_back(e213);
				rt428.e.push_back(e214);
				rt428.e.push_back(e62);
				rt428.e.push_back(e50);
				rt428.e.push_back(e3);
				rt428.calc_arity(nullptr);
				sprawformtree ft427 = std::make_shared<raw_form_tree>(elem::NONE, rt428);
				sprawformtree ft425 = std::make_shared<raw_form_tree>(elem::EXISTS, ft426, ft427);
				sprawformtree ft424 = std::make_shared<raw_form_tree>(elem::NOT, ft425);
				sprawformtree ft415 = std::make_shared<raw_form_tree>(elem::AND, ft416, ft424);
				raw_term rt431;
				rt431.neg = false;
				rt431.extype = raw_term::REL;
				rt431.e.push_back(e320);
				rt431.e.push_back(e1);
				rt431.e.push_back(e213);
				rt431.e.push_back(e214);
				rt431.e.push_back(e62);
				rt431.e.push_back(e3);
				rt431.calc_arity(nullptr);
				sprawformtree ft430 = std::make_shared<raw_form_tree>(elem::NONE, rt431);
				sprawformtree ft429 = std::make_shared<raw_form_tree>(elem::NOT, ft430);
				sprawformtree ft414 = std::make_shared<raw_form_tree>(elem::AND, ft415, ft429);
				raw_rule rr432;
				rr432.h.push_back(rt413);
				rr432.set_prft(ft414);
				raw_term rt433;
				rt433.neg = false;
				rt433.extype = raw_term::REL;
				rt433.e.push_back(e311);
				rt433.e.push_back(e1);
				rt433.e.push_back(e213);
				rt433.e.push_back(e214);
				rt433.e.push_back(e62);
				rt433.e.push_back(e50);
				rt433.e.push_back(e3);
				rt433.calc_arity(nullptr);
				raw_term rt440;
				rt440.neg = false;
				rt440.extype = raw_term::REL;
				rt440.e.push_back(e153);
				rt440.e.push_back(e1);
				rt440.e.push_back(e50);
				rt440.e.push_back(e3);
				rt440.calc_arity(nullptr);
				sprawformtree ft439 = std::make_shared<raw_form_tree>(elem::NONE, rt440);
				raw_term rt442;
				rt442.neg = false;
				rt442.extype = raw_term::REL;
				rt442.e.push_back(e306);
				rt442.e.push_back(e1);
				rt442.e.push_back(e213);
				rt442.e.push_back(e214);
				rt442.e.push_back(e198);
				rt442.e.push_back(e199);
				rt442.e.push_back(e62);
				rt442.e.push_back(e3);
				rt442.calc_arity(nullptr);
				sprawformtree ft441 = std::make_shared<raw_form_tree>(elem::NONE, rt442);
				sprawformtree ft438 = std::make_shared<raw_form_tree>(elem::AND, ft439, ft441);
				raw_term rt444;
				rt444.neg = false;
				rt444.extype = raw_term::REL;
				rt444.e.push_back(e156);
				rt444.e.push_back(e1);
				rt444.e.push_back(e198);
				rt444.e.push_back(e3);
				rt444.calc_arity(nullptr);
				sprawformtree ft443 = std::make_shared<raw_form_tree>(elem::NONE, rt444);
				sprawformtree ft437 = std::make_shared<raw_form_tree>(elem::AND, ft438, ft443);
				raw_term rt446;
				rt446.neg = false;
				rt446.extype = raw_term::REL;
				rt446.e.push_back(e156);
				rt446.e.push_back(e1);
				rt446.e.push_back(e199);
				rt446.e.push_back(e3);
				rt446.calc_arity(nullptr);
				sprawformtree ft445 = std::make_shared<raw_form_tree>(elem::NONE, rt446);
				sprawformtree ft436 = std::make_shared<raw_form_tree>(elem::AND, ft437, ft445);
				sprawformtree ft449 = std::make_shared<raw_form_tree>(elem::VAR, e50);
				raw_term rt451;
				rt451.neg = false;
				rt451.extype = raw_term::REL;
				rt451.e.push_back(e311);
				rt451.e.push_back(e1);
				rt451.e.push_back(e213);
				rt451.e.push_back(e214);
				rt451.e.push_back(e62);
				rt451.e.push_back(e50);
				rt451.e.push_back(e3);
				rt451.calc_arity(nullptr);
				sprawformtree ft450 = std::make_shared<raw_form_tree>(elem::NONE, rt451);
				sprawformtree ft448 = std::make_shared<raw_form_tree>(elem::EXISTS, ft449, ft450);
				sprawformtree ft447 = std::make_shared<raw_form_tree>(elem::NOT, ft448);
				sprawformtree ft435 = std::make_shared<raw_form_tree>(elem::AND, ft436, ft447);
				raw_term rt454;
				rt454.neg = false;
				rt454.extype = raw_term::REL;
				rt454.e.push_back(e320);
				rt454.e.push_back(e1);
				rt454.e.push_back(e213);
				rt454.e.push_back(e214);
				rt454.e.push_back(e62);
				rt454.e.push_back(e3);
				rt454.calc_arity(nullptr);
				sprawformtree ft453 = std::make_shared<raw_form_tree>(elem::NONE, rt454);
				sprawformtree ft452 = std::make_shared<raw_form_tree>(elem::NOT, ft453);
				sprawformtree ft434 = std::make_shared<raw_form_tree>(elem::AND, ft435, ft452);
				raw_rule rr455;
				rr455.h.push_back(rt433);
				rr455.set_prft(ft434);
				raw_term rt456;
				rt456.neg = true;
				rt456.extype = raw_term::REL;
				rt456.e.push_back(e306);
				rt456.e.push_back(e1);
				rt456.e.push_back(e213);
				rt456.e.push_back(e214);
				rt456.e.push_back(e198);
				rt456.e.push_back(e199);
				rt456.e.push_back(e62);
				rt456.e.push_back(e3);
				rt456.calc_arity(nullptr);
				raw_term rt457;
				rt457.neg = true;
				rt457.extype = raw_term::REL;
				rt457.e.push_back(e306);
				rt457.e.push_back(e1);
				rt457.e.push_back(e213);
				rt457.e.push_back(e214);
				rt457.e.push_back(e198);
				rt457.e.push_back(e199);
				rt457.e.push_back(e62);
				rt457.e.push_back(e50);
				rt457.e.push_back(e3);
				rt457.calc_arity(nullptr);
				raw_term rt460;
				rt460.neg = false;
				rt460.extype = raw_term::REL;
				rt460.e.push_back(e311);
				rt460.e.push_back(e1);
				rt460.e.push_back(e213);
				rt460.e.push_back(e214);
				rt460.e.push_back(e62);
				rt460.e.push_back(e165);
				rt460.e.push_back(e3);
				rt460.calc_arity(nullptr);
				sprawformtree ft459 = std::make_shared<raw_form_tree>(elem::NONE, rt460);
				raw_term rt462;
				rt462.neg = false;
				rt462.extype = raw_term::REL;
				rt462.e.push_back(e320);
				rt462.e.push_back(e1);
				rt462.e.push_back(e213);
				rt462.e.push_back(e214);
				rt462.e.push_back(e62);
				rt462.e.push_back(e3);
				rt462.calc_arity(nullptr);
				sprawformtree ft461 = std::make_shared<raw_form_tree>(elem::NONE, rt462);
				sprawformtree ft458 = std::make_shared<raw_form_tree>(elem::ALT, ft459, ft461);
				raw_rule rr463;
				rr463.h.push_back(rt456);
				rr463.h.push_back(rt457);
				rr463.set_prft(ft458);
				elem e464;
				e464.type = elem::SYM;
				e464.e = d.get_lexeme("ASSOC_LIST0");
				elem e465;
				e465.type = elem::VAR;
				e465.e = d.get_lexeme("?ts");
				elem e466;
				e466.type = elem::VAR;
				e466.e = d.get_lexeme("?us");
				raw_term rt467;
				rt467.neg = false;
				rt467.extype = raw_term::REL;
				rt467.e.push_back(e464);
				rt467.e.push_back(e1);
				rt467.e.push_back(e465);
				rt467.e.push_back(e198);
				rt467.e.push_back(e199);
				rt467.e.push_back(e465);
				rt467.e.push_back(e466);
				rt467.e.push_back(e3);
				rt467.calc_arity(nullptr);
				elem e471;
				e471.type = elem::SYM;
				e471.e = d.get_lexeme("ASSOC_LIST");
				raw_term rt472;
				rt472.neg = false;
				rt472.extype = raw_term::REL;
				rt472.e.push_back(e471);
				rt472.e.push_back(e1);
				rt472.e.push_back(e198);
				rt472.e.push_back(e199);
				rt472.e.push_back(e465);
				rt472.e.push_back(e3);
				rt472.calc_arity(nullptr);
				sprawformtree ft470 = std::make_shared<raw_form_tree>(elem::NONE, rt472);
				raw_term rt474;
				rt474.neg = false;
				rt474.extype = raw_term::REL;
				rt474.e.push_back(e156);
				rt474.e.push_back(e1);
				rt474.e.push_back(e466);
				rt474.e.push_back(e3);
				rt474.calc_arity(nullptr);
				sprawformtree ft473 = std::make_shared<raw_form_tree>(elem::NONE, rt474);
				sprawformtree ft469 = std::make_shared<raw_form_tree>(elem::AND, ft470, ft473);
				sprawformtree ft477 = std::make_shared<raw_form_tree>(elem::VAR, e165);
				raw_term rt479;
				rt479.neg = false;
				rt479.extype = raw_term::REL;
				rt479.e.push_back(e471);
				rt479.e.push_back(e1);
				rt479.e.push_back(e198);
				rt479.e.push_back(e199);
				rt479.e.push_back(e465);
				rt479.e.push_back(e165);
				rt479.e.push_back(e3);
				rt479.calc_arity(nullptr);
				sprawformtree ft478 = std::make_shared<raw_form_tree>(elem::NONE, rt479);
				sprawformtree ft476 = std::make_shared<raw_form_tree>(elem::EXISTS, ft477, ft478);
				sprawformtree ft475 = std::make_shared<raw_form_tree>(elem::NOT, ft476);
				sprawformtree ft468 = std::make_shared<raw_form_tree>(elem::AND, ft469, ft475);
				raw_rule rr480;
				rr480.h.push_back(rt467);
				rr480.set_prft(ft468);
				elem e481;
				e481.type = elem::VAR;
				e481.e = d.get_lexeme("?ts_hd");
				raw_term rt482;
				rt482.neg = false;
				rt482.extype = raw_term::REL;
				rt482.e.push_back(e311);
				rt482.e.push_back(e1);
				rt482.e.push_back(e198);
				rt482.e.push_back(e199);
				rt482.e.push_back(e481);
				rt482.e.push_back(e3);
				rt482.calc_arity(nullptr);
				elem e483;
				e483.type = elem::SYM;
				e483.e = d.get_lexeme("ASSOC_LIST1");
				elem e484;
				e484.type = elem::VAR;
				e484.e = d.get_lexeme("?ots");
				raw_term rt485;
				rt485.neg = false;
				rt485.extype = raw_term::REL;
				rt485.e.push_back(e483);
				rt485.e.push_back(e1);
				rt485.e.push_back(e484);
				rt485.e.push_back(e198);
				rt485.e.push_back(e199);
				rt485.e.push_back(e465);
				rt485.e.push_back(e466);
				rt485.e.push_back(e3);
				rt485.calc_arity(nullptr);
				raw_term rt489;
				rt489.neg = false;
				rt489.extype = raw_term::REL;
				rt489.e.push_back(e464);
				rt489.e.push_back(e1);
				rt489.e.push_back(e484);
				rt489.e.push_back(e198);
				rt489.e.push_back(e199);
				rt489.e.push_back(e465);
				rt489.e.push_back(e466);
				rt489.e.push_back(e3);
				rt489.calc_arity(nullptr);
				sprawformtree ft488 = std::make_shared<raw_form_tree>(elem::NONE, rt489);
				elem e491;
				e491.type = elem::VAR;
				e491.e = d.get_lexeme("?ts_tl");
				raw_term rt492;
				rt492.neg = false;
				rt492.extype = raw_term::REL;
				rt492.e.push_back(e156);
				rt492.e.push_back(e1);
				rt492.e.push_back(e465);
				rt492.e.push_back(e481);
				rt492.e.push_back(e491);
				rt492.e.push_back(e3);
				rt492.calc_arity(nullptr);
				sprawformtree ft490 = std::make_shared<raw_form_tree>(elem::NONE, rt492);
				sprawformtree ft487 = std::make_shared<raw_form_tree>(elem::AND, ft488, ft490);
				sprawformtree ft495 = std::make_shared<raw_form_tree>(elem::VAR, e165);
				raw_term rt497;
				rt497.neg = false;
				rt497.extype = raw_term::REL;
				rt497.e.push_back(e471);
				rt497.e.push_back(e1);
				rt497.e.push_back(e198);
				rt497.e.push_back(e199);
				rt497.e.push_back(e484);
				rt497.e.push_back(e165);
				rt497.e.push_back(e3);
				rt497.calc_arity(nullptr);
				sprawformtree ft496 = std::make_shared<raw_form_tree>(elem::NONE, rt497);
				sprawformtree ft494 = std::make_shared<raw_form_tree>(elem::EXISTS, ft495, ft496);
				sprawformtree ft493 = std::make_shared<raw_form_tree>(elem::NOT, ft494);
				sprawformtree ft486 = std::make_shared<raw_form_tree>(elem::AND, ft487, ft493);
				raw_rule rr498;
				rr498.h.push_back(rt482);
				rr498.h.push_back(rt485);
				rr498.set_prft(ft486);
				elem e499;
				e499.type = elem::VAR;
				e499.e = d.get_lexeme("?nus");
				raw_term rt500;
				rt500.neg = false;
				rt500.extype = raw_term::REL;
				rt500.e.push_back(e464);
				rt500.e.push_back(e1);
				rt500.e.push_back(e484);
				rt500.e.push_back(e198);
				rt500.e.push_back(e199);
				rt500.e.push_back(e491);
				rt500.e.push_back(e499);
				rt500.e.push_back(e3);
				rt500.calc_arity(nullptr);
				raw_term rt506;
				rt506.neg = false;
				rt506.extype = raw_term::REL;
				rt506.e.push_back(e483);
				rt506.e.push_back(e1);
				rt506.e.push_back(e484);
				rt506.e.push_back(e198);
				rt506.e.push_back(e199);
				rt506.e.push_back(e465);
				rt506.e.push_back(e466);
				rt506.e.push_back(e3);
				rt506.calc_arity(nullptr);
				sprawformtree ft505 = std::make_shared<raw_form_tree>(elem::NONE, rt506);
				raw_term rt508;
				rt508.neg = false;
				rt508.extype = raw_term::REL;
				rt508.e.push_back(e156);
				rt508.e.push_back(e1);
				rt508.e.push_back(e465);
				rt508.e.push_back(e481);
				rt508.e.push_back(e491);
				rt508.e.push_back(e3);
				rt508.calc_arity(nullptr);
				sprawformtree ft507 = std::make_shared<raw_form_tree>(elem::NONE, rt508);
				sprawformtree ft504 = std::make_shared<raw_form_tree>(elem::AND, ft505, ft507);
				elem e510;
				e510.type = elem::VAR;
				e510.e = d.get_lexeme("?nus_hd");
				raw_term rt511;
				rt511.neg = false;
				rt511.extype = raw_term::REL;
				rt511.e.push_back(e311);
				rt511.e.push_back(e1);
				rt511.e.push_back(e198);
				rt511.e.push_back(e199);
				rt511.e.push_back(e481);
				rt511.e.push_back(e510);
				rt511.e.push_back(e3);
				rt511.calc_arity(nullptr);
				sprawformtree ft509 = std::make_shared<raw_form_tree>(elem::NONE, rt511);
				sprawformtree ft503 = std::make_shared<raw_form_tree>(elem::AND, ft504, ft509);
				raw_term rt513;
				rt513.neg = false;
				rt513.extype = raw_term::REL;
				rt513.e.push_back(e156);
				rt513.e.push_back(e1);
				rt513.e.push_back(e499);
				rt513.e.push_back(e510);
				rt513.e.push_back(e466);
				rt513.e.push_back(e3);
				rt513.calc_arity(nullptr);
				sprawformtree ft512 = std::make_shared<raw_form_tree>(elem::NONE, rt513);
				sprawformtree ft502 = std::make_shared<raw_form_tree>(elem::AND, ft503, ft512);
				sprawformtree ft516 = std::make_shared<raw_form_tree>(elem::VAR, e165);
				raw_term rt518;
				rt518.neg = false;
				rt518.extype = raw_term::REL;
				rt518.e.push_back(e471);
				rt518.e.push_back(e1);
				rt518.e.push_back(e198);
				rt518.e.push_back(e199);
				rt518.e.push_back(e484);
				rt518.e.push_back(e165);
				rt518.e.push_back(e3);
				rt518.calc_arity(nullptr);
				sprawformtree ft517 = std::make_shared<raw_form_tree>(elem::NONE, rt518);
				sprawformtree ft515 = std::make_shared<raw_form_tree>(elem::EXISTS, ft516, ft517);
				sprawformtree ft514 = std::make_shared<raw_form_tree>(elem::NOT, ft515);
				sprawformtree ft501 = std::make_shared<raw_form_tree>(elem::AND, ft502, ft514);
				raw_rule rr519;
				rr519.h.push_back(rt500);
				rr519.set_prft(ft501);
				raw_term rt520;
				rt520.neg = false;
				rt520.extype = raw_term::REL;
				rt520.e.push_back(e253);
				rt520.e.push_back(e1);
				rt520.e.push_back(e466);
				rt520.e.push_back(e3);
				rt520.calc_arity(nullptr);
				elem e521;
				e521.type = elem::SYM;
				e521.e = d.get_lexeme("ASSOC_LIST2");
				raw_term rt522;
				rt522.neg = false;
				rt522.extype = raw_term::REL;
				rt522.e.push_back(e521);
				rt522.e.push_back(e1);
				rt522.e.push_back(e484);
				rt522.e.push_back(e198);
				rt522.e.push_back(e199);
				rt522.e.push_back(e465);
				rt522.e.push_back(e466);
				rt522.e.push_back(e3);
				rt522.calc_arity(nullptr);
				raw_term rt526;
				rt526.neg = false;
				rt526.extype = raw_term::REL;
				rt526.e.push_back(e464);
				rt526.e.push_back(e1);
				rt526.e.push_back(e484);
				rt526.e.push_back(e198);
				rt526.e.push_back(e199);
				rt526.e.push_back(e465);
				rt526.e.push_back(e466);
				rt526.e.push_back(e3);
				rt526.calc_arity(nullptr);
				sprawformtree ft525 = std::make_shared<raw_form_tree>(elem::NONE, rt526);
				raw_term rt528;
				rt528.neg = false;
				rt528.extype = raw_term::REL;
				rt528.e.push_back(e156);
				rt528.e.push_back(e1);
				rt528.e.push_back(e465);
				rt528.e.push_back(e3);
				rt528.calc_arity(nullptr);
				sprawformtree ft527 = std::make_shared<raw_form_tree>(elem::NONE, rt528);
				sprawformtree ft524 = std::make_shared<raw_form_tree>(elem::AND, ft525, ft527);
				sprawformtree ft531 = std::make_shared<raw_form_tree>(elem::VAR, e165);
				raw_term rt533;
				rt533.neg = false;
				rt533.extype = raw_term::REL;
				rt533.e.push_back(e471);
				rt533.e.push_back(e1);
				rt533.e.push_back(e198);
				rt533.e.push_back(e199);
				rt533.e.push_back(e484);
				rt533.e.push_back(e165);
				rt533.e.push_back(e3);
				rt533.calc_arity(nullptr);
				sprawformtree ft532 = std::make_shared<raw_form_tree>(elem::NONE, rt533);
				sprawformtree ft530 = std::make_shared<raw_form_tree>(elem::EXISTS, ft531, ft532);
				sprawformtree ft529 = std::make_shared<raw_form_tree>(elem::NOT, ft530);
				sprawformtree ft523 = std::make_shared<raw_form_tree>(elem::AND, ft524, ft529);
				raw_rule rr534;
				rr534.h.push_back(rt520);
				rr534.h.push_back(rt522);
				rr534.set_prft(ft523);
				raw_term rt535;
				rt535.neg = false;
				rt535.extype = raw_term::REL;
				rt535.e.push_back(e471);
				rt535.e.push_back(e1);
				rt535.e.push_back(e198);
				rt535.e.push_back(e199);
				rt535.e.push_back(e484);
				rt535.e.push_back(e499);
				rt535.e.push_back(e3);
				rt535.calc_arity(nullptr);
				raw_term rt540;
				rt540.neg = false;
				rt540.extype = raw_term::REL;
				rt540.e.push_back(e521);
				rt540.e.push_back(e1);
				rt540.e.push_back(e484);
				rt540.e.push_back(e198);
				rt540.e.push_back(e199);
				rt540.e.push_back(e465);
				rt540.e.push_back(e466);
				rt540.e.push_back(e3);
				rt540.calc_arity(nullptr);
				sprawformtree ft539 = std::make_shared<raw_form_tree>(elem::NONE, rt540);
				raw_term rt542;
				rt542.neg = false;
				rt542.extype = raw_term::REL;
				rt542.e.push_back(e266);
				rt542.e.push_back(e1);
				rt542.e.push_back(e466);
				rt542.e.push_back(e499);
				rt542.e.push_back(e3);
				rt542.calc_arity(nullptr);
				sprawformtree ft541 = std::make_shared<raw_form_tree>(elem::NONE, rt542);
				sprawformtree ft538 = std::make_shared<raw_form_tree>(elem::AND, ft539, ft541);
				raw_term rt544;
				rt544.neg = false;
				rt544.extype = raw_term::REL;
				rt544.e.push_back(e156);
				rt544.e.push_back(e1);
				rt544.e.push_back(e465);
				rt544.e.push_back(e3);
				rt544.calc_arity(nullptr);
				sprawformtree ft543 = std::make_shared<raw_form_tree>(elem::NONE, rt544);
				sprawformtree ft537 = std::make_shared<raw_form_tree>(elem::AND, ft538, ft543);
				sprawformtree ft547 = std::make_shared<raw_form_tree>(elem::VAR, e165);
				raw_term rt549;
				rt549.neg = false;
				rt549.extype = raw_term::REL;
				rt549.e.push_back(e471);
				rt549.e.push_back(e1);
				rt549.e.push_back(e198);
				rt549.e.push_back(e199);
				rt549.e.push_back(e484);
				rt549.e.push_back(e165);
				rt549.e.push_back(e3);
				rt549.calc_arity(nullptr);
				sprawformtree ft548 = std::make_shared<raw_form_tree>(elem::NONE, rt549);
				sprawformtree ft546 = std::make_shared<raw_form_tree>(elem::EXISTS, ft547, ft548);
				sprawformtree ft545 = std::make_shared<raw_form_tree>(elem::NOT, ft546);
				sprawformtree ft536 = std::make_shared<raw_form_tree>(elem::AND, ft537, ft545);
				raw_rule rr550;
				rr550.h.push_back(rt535);
				rr550.set_prft(ft536);
				raw_term rt551;
				rt551.neg = true;
				rt551.extype = raw_term::REL;
				rt551.e.push_back(e464);
				rt551.e.push_back(e1);
				rt551.e.push_back(e484);
				rt551.e.push_back(e198);
				rt551.e.push_back(e199);
				rt551.e.push_back(e491);
				rt551.e.push_back(e499);
				rt551.e.push_back(e3);
				rt551.calc_arity(nullptr);
				raw_term rt552;
				rt552.neg = true;
				rt552.extype = raw_term::REL;
				rt552.e.push_back(e483);
				rt552.e.push_back(e1);
				rt552.e.push_back(e484);
				rt552.e.push_back(e198);
				rt552.e.push_back(e199);
				rt552.e.push_back(e465);
				rt552.e.push_back(e466);
				rt552.e.push_back(e3);
				rt552.calc_arity(nullptr);
				raw_term rt553;
				rt553.neg = true;
				rt553.extype = raw_term::REL;
				rt553.e.push_back(e521);
				rt553.e.push_back(e1);
				rt553.e.push_back(e484);
				rt553.e.push_back(e198);
				rt553.e.push_back(e199);
				rt553.e.push_back(e465);
				rt553.e.push_back(e466);
				rt553.e.push_back(e3);
				rt553.calc_arity(nullptr);
				raw_term rt555;
				rt555.neg = false;
				rt555.extype = raw_term::REL;
				rt555.e.push_back(e471);
				rt555.e.push_back(e1);
				rt555.e.push_back(e198);
				rt555.e.push_back(e199);
				rt555.e.push_back(e484);
				rt555.e.push_back(e165);
				rt555.e.push_back(e3);
				rt555.calc_arity(nullptr);
				sprawformtree ft554 = std::make_shared<raw_form_tree>(elem::NONE, rt555);
				raw_rule rr556;
				rr556.h.push_back(rt551);
				rr556.h.push_back(rt552);
				rr556.h.push_back(rt553);
				rr556.set_prft(ft554);
				elem e557;
				e557.type = elem::SYM;
				e557.e = d.get_lexeme("IS_CONSISTENT0");
				raw_term rt558;
				rt558.neg = false;
				rt558.extype = raw_term::REL;
				rt558.e.push_back(e557);
				rt558.e.push_back(e1);
				rt558.e.push_back(e198);
				rt558.e.push_back(e199);
				rt558.e.push_back(e198);
				rt558.e.push_back(e199);
				rt558.e.push_back(e62);
				rt558.e.push_back(e50);
				rt558.e.push_back(e3);
				rt558.calc_arity(nullptr);
				elem e562;
				e562.type = elem::SYM;
				e562.e = d.get_lexeme("IS_ASSOC_CONSISTENT");
				raw_term rt563;
				rt563.neg = false;
				rt563.extype = raw_term::REL;
				rt563.e.push_back(e562);
				rt563.e.push_back(e1);
				rt563.e.push_back(e198);
				rt563.e.push_back(e199);
				rt563.e.push_back(e62);
				rt563.e.push_back(e50);
				rt563.e.push_back(e3);
				rt563.calc_arity(nullptr);
				sprawformtree ft561 = std::make_shared<raw_form_tree>(elem::NONE, rt563);
				elem e566;
				e566.type = elem::SYM;
				e566.e = d.get_lexeme("CONSISTENT");
				raw_term rt567;
				rt567.neg = false;
				rt567.extype = raw_term::REL;
				rt567.e.push_back(e566);
				rt567.e.push_back(e1);
				rt567.e.push_back(e198);
				rt567.e.push_back(e199);
				rt567.e.push_back(e62);
				rt567.e.push_back(e50);
				rt567.e.push_back(e3);
				rt567.calc_arity(nullptr);
				sprawformtree ft565 = std::make_shared<raw_form_tree>(elem::NONE, rt567);
				sprawformtree ft564 = std::make_shared<raw_form_tree>(elem::NOT, ft565);
				sprawformtree ft560 = std::make_shared<raw_form_tree>(elem::AND, ft561, ft564);
				elem e570;
				e570.type = elem::SYM;
				e570.e = d.get_lexeme("NOT_CONSISTENT");
				raw_term rt571;
				rt571.neg = false;
				rt571.extype = raw_term::REL;
				rt571.e.push_back(e570);
				rt571.e.push_back(e1);
				rt571.e.push_back(e198);
				rt571.e.push_back(e199);
				rt571.e.push_back(e62);
				rt571.e.push_back(e50);
				rt571.e.push_back(e3);
				rt571.calc_arity(nullptr);
				sprawformtree ft569 = std::make_shared<raw_form_tree>(elem::NONE, rt571);
				sprawformtree ft568 = std::make_shared<raw_form_tree>(elem::NOT, ft569);
				sprawformtree ft559 = std::make_shared<raw_form_tree>(elem::AND, ft560, ft568);
				raw_rule rr572;
				rr572.h.push_back(rt558);
				rr572.set_prft(ft559);
				raw_term rt573;
				rt573.neg = false;
				rt573.extype = raw_term::REL;
				rt573.e.push_back(e557);
				rt573.e.push_back(e1);
				rt573.e.push_back(e213);
				rt573.e.push_back(e214);
				rt573.e.push_back(e215);
				rt573.e.push_back(e221);
				rt573.e.push_back(e62);
				rt573.e.push_back(e50);
				rt573.e.push_back(e3);
				rt573.calc_arity(nullptr);
				raw_term rt579;
				rt579.neg = false;
				rt579.extype = raw_term::REL;
				rt579.e.push_back(e156);
				rt579.e.push_back(e1);
				rt579.e.push_back(e198);
				rt579.e.push_back(e62);
				rt579.e.push_back(e215);
				rt579.e.push_back(e3);
				rt579.calc_arity(nullptr);
				sprawformtree ft578 = std::make_shared<raw_form_tree>(elem::NONE, rt579);
				raw_term rt581;
				rt581.neg = false;
				rt581.extype = raw_term::REL;
				rt581.e.push_back(e156);
				rt581.e.push_back(e1);
				rt581.e.push_back(e199);
				rt581.e.push_back(e50);
				rt581.e.push_back(e221);
				rt581.e.push_back(e3);
				rt581.calc_arity(nullptr);
				sprawformtree ft580 = std::make_shared<raw_form_tree>(elem::NONE, rt581);
				sprawformtree ft577 = std::make_shared<raw_form_tree>(elem::AND, ft578, ft580);
				raw_term rt583;
				rt583.neg = false;
				rt583.extype = raw_term::REL;
				rt583.e.push_back(e557);
				rt583.e.push_back(e1);
				rt583.e.push_back(e213);
				rt583.e.push_back(e214);
				rt583.e.push_back(e198);
				rt583.e.push_back(e199);
				rt583.e.push_back(e62);
				rt583.e.push_back(e50);
				rt583.e.push_back(e3);
				rt583.calc_arity(nullptr);
				sprawformtree ft582 = std::make_shared<raw_form_tree>(elem::NONE, rt583);
				sprawformtree ft576 = std::make_shared<raw_form_tree>(elem::AND, ft577, ft582);
				raw_term rt586;
				rt586.neg = false;
				rt586.extype = raw_term::REL;
				rt586.e.push_back(e566);
				rt586.e.push_back(e1);
				rt586.e.push_back(e213);
				rt586.e.push_back(e214);
				rt586.e.push_back(e62);
				rt586.e.push_back(e50);
				rt586.e.push_back(e3);
				rt586.calc_arity(nullptr);
				sprawformtree ft585 = std::make_shared<raw_form_tree>(elem::NONE, rt586);
				sprawformtree ft584 = std::make_shared<raw_form_tree>(elem::NOT, ft585);
				sprawformtree ft575 = std::make_shared<raw_form_tree>(elem::AND, ft576, ft584);
				raw_term rt589;
				rt589.neg = false;
				rt589.extype = raw_term::REL;
				rt589.e.push_back(e570);
				rt589.e.push_back(e1);
				rt589.e.push_back(e213);
				rt589.e.push_back(e214);
				rt589.e.push_back(e62);
				rt589.e.push_back(e50);
				rt589.e.push_back(e3);
				rt589.calc_arity(nullptr);
				sprawformtree ft588 = std::make_shared<raw_form_tree>(elem::NONE, rt589);
				sprawformtree ft587 = std::make_shared<raw_form_tree>(elem::NOT, ft588);
				sprawformtree ft574 = std::make_shared<raw_form_tree>(elem::AND, ft575, ft587);
				raw_rule rr590;
				rr590.h.push_back(rt573);
				rr590.set_prft(ft574);
				raw_term rt591;
				rt591.neg = false;
				rt591.extype = raw_term::REL;
				rt591.e.push_back(e557);
				rt591.e.push_back(e1);
				rt591.e.push_back(e213);
				rt591.e.push_back(e214);
				rt591.e.push_back(e215);
				rt591.e.push_back(e221);
				rt591.e.push_back(e62);
				rt591.e.push_back(e50);
				rt591.e.push_back(e3);
				rt591.calc_arity(nullptr);
				raw_term rt599;
				rt599.neg = false;
				rt599.extype = raw_term::REL;
				rt599.e.push_back(e156);
				rt599.e.push_back(e1);
				rt599.e.push_back(e198);
				rt599.e.push_back(e62);
				rt599.e.push_back(e215);
				rt599.e.push_back(e3);
				rt599.calc_arity(nullptr);
				sprawformtree ft598 = std::make_shared<raw_form_tree>(elem::NONE, rt599);
				sprawformtree ft597 = std::make_shared<raw_form_tree>(elem::NOT, ft598);
				raw_term rt601;
				rt601.neg = false;
				rt601.extype = raw_term::REL;
				rt601.e.push_back(e156);
				rt601.e.push_back(e1);
				rt601.e.push_back(e198);
				rt601.e.push_back(e224);
				rt601.e.push_back(e215);
				rt601.e.push_back(e3);
				rt601.calc_arity(nullptr);
				sprawformtree ft600 = std::make_shared<raw_form_tree>(elem::NONE, rt601);
				sprawformtree ft596 = std::make_shared<raw_form_tree>(elem::AND, ft597, ft600);
				elem e603;
				e603.type = elem::VAR;
				e603.e = d.get_lexeme("?ys_hd");
				raw_term rt604;
				rt604.neg = false;
				rt604.extype = raw_term::REL;
				rt604.e.push_back(e156);
				rt604.e.push_back(e1);
				rt604.e.push_back(e199);
				rt604.e.push_back(e603);
				rt604.e.push_back(e221);
				rt604.e.push_back(e3);
				rt604.calc_arity(nullptr);
				sprawformtree ft602 = std::make_shared<raw_form_tree>(elem::NONE, rt604);
				sprawformtree ft595 = std::make_shared<raw_form_tree>(elem::AND, ft596, ft602);
				raw_term rt606;
				rt606.neg = false;
				rt606.extype = raw_term::REL;
				rt606.e.push_back(e557);
				rt606.e.push_back(e1);
				rt606.e.push_back(e213);
				rt606.e.push_back(e214);
				rt606.e.push_back(e198);
				rt606.e.push_back(e199);
				rt606.e.push_back(e62);
				rt606.e.push_back(e50);
				rt606.e.push_back(e3);
				rt606.calc_arity(nullptr);
				sprawformtree ft605 = std::make_shared<raw_form_tree>(elem::NONE, rt606);
				sprawformtree ft594 = std::make_shared<raw_form_tree>(elem::AND, ft595, ft605);
				raw_term rt609;
				rt609.neg = false;
				rt609.extype = raw_term::REL;
				rt609.e.push_back(e566);
				rt609.e.push_back(e1);
				rt609.e.push_back(e213);
				rt609.e.push_back(e214);
				rt609.e.push_back(e62);
				rt609.e.push_back(e50);
				rt609.e.push_back(e3);
				rt609.calc_arity(nullptr);
				sprawformtree ft608 = std::make_shared<raw_form_tree>(elem::NONE, rt609);
				sprawformtree ft607 = std::make_shared<raw_form_tree>(elem::NOT, ft608);
				sprawformtree ft593 = std::make_shared<raw_form_tree>(elem::AND, ft594, ft607);
				raw_term rt612;
				rt612.neg = false;
				rt612.extype = raw_term::REL;
				rt612.e.push_back(e570);
				rt612.e.push_back(e1);
				rt612.e.push_back(e213);
				rt612.e.push_back(e214);
				rt612.e.push_back(e62);
				rt612.e.push_back(e50);
				rt612.e.push_back(e3);
				rt612.calc_arity(nullptr);
				sprawformtree ft611 = std::make_shared<raw_form_tree>(elem::NONE, rt612);
				sprawformtree ft610 = std::make_shared<raw_form_tree>(elem::NOT, ft611);
				sprawformtree ft592 = std::make_shared<raw_form_tree>(elem::AND, ft593, ft610);
				raw_rule rr613;
				rr613.h.push_back(rt591);
				rr613.set_prft(ft592);
				raw_term rt614;
				rt614.neg = false;
				rt614.extype = raw_term::REL;
				rt614.e.push_back(e570);
				rt614.e.push_back(e1);
				rt614.e.push_back(e213);
				rt614.e.push_back(e214);
				rt614.e.push_back(e62);
				rt614.e.push_back(e50);
				rt614.e.push_back(e3);
				rt614.calc_arity(nullptr);
				raw_term rt621;
				rt621.neg = false;
				rt621.extype = raw_term::REL;
				rt621.e.push_back(e156);
				rt621.e.push_back(e1);
				rt621.e.push_back(e198);
				rt621.e.push_back(e62);
				rt621.e.push_back(e215);
				rt621.e.push_back(e3);
				rt621.calc_arity(nullptr);
				sprawformtree ft620 = std::make_shared<raw_form_tree>(elem::NONE, rt621);
				raw_term rt624;
				rt624.neg = false;
				rt624.extype = raw_term::REL;
				rt624.e.push_back(e156);
				rt624.e.push_back(e1);
				rt624.e.push_back(e199);
				rt624.e.push_back(e50);
				rt624.e.push_back(e221);
				rt624.e.push_back(e3);
				rt624.calc_arity(nullptr);
				sprawformtree ft623 = std::make_shared<raw_form_tree>(elem::NONE, rt624);
				sprawformtree ft622 = std::make_shared<raw_form_tree>(elem::NOT, ft623);
				sprawformtree ft619 = std::make_shared<raw_form_tree>(elem::AND, ft620, ft622);
				elem e626;
				e626.type = elem::VAR;
				e626.e = d.get_lexeme("?ay");
				raw_term rt627;
				rt627.neg = false;
				rt627.extype = raw_term::REL;
				rt627.e.push_back(e156);
				rt627.e.push_back(e1);
				rt627.e.push_back(e199);
				rt627.e.push_back(e626);
				rt627.e.push_back(e221);
				rt627.e.push_back(e3);
				rt627.calc_arity(nullptr);
				sprawformtree ft625 = std::make_shared<raw_form_tree>(elem::NONE, rt627);
				sprawformtree ft618 = std::make_shared<raw_form_tree>(elem::AND, ft619, ft625);
				raw_term rt629;
				rt629.neg = false;
				rt629.extype = raw_term::REL;
				rt629.e.push_back(e557);
				rt629.e.push_back(e1);
				rt629.e.push_back(e213);
				rt629.e.push_back(e214);
				rt629.e.push_back(e198);
				rt629.e.push_back(e199);
				rt629.e.push_back(e62);
				rt629.e.push_back(e50);
				rt629.e.push_back(e3);
				rt629.calc_arity(nullptr);
				sprawformtree ft628 = std::make_shared<raw_form_tree>(elem::NONE, rt629);
				sprawformtree ft617 = std::make_shared<raw_form_tree>(elem::AND, ft618, ft628);
				raw_term rt632;
				rt632.neg = false;
				rt632.extype = raw_term::REL;
				rt632.e.push_back(e566);
				rt632.e.push_back(e1);
				rt632.e.push_back(e213);
				rt632.e.push_back(e214);
				rt632.e.push_back(e62);
				rt632.e.push_back(e50);
				rt632.e.push_back(e3);
				rt632.calc_arity(nullptr);
				sprawformtree ft631 = std::make_shared<raw_form_tree>(elem::NONE, rt632);
				sprawformtree ft630 = std::make_shared<raw_form_tree>(elem::NOT, ft631);
				sprawformtree ft616 = std::make_shared<raw_form_tree>(elem::AND, ft617, ft630);
				raw_term rt635;
				rt635.neg = false;
				rt635.extype = raw_term::REL;
				rt635.e.push_back(e570);
				rt635.e.push_back(e1);
				rt635.e.push_back(e213);
				rt635.e.push_back(e214);
				rt635.e.push_back(e62);
				rt635.e.push_back(e50);
				rt635.e.push_back(e3);
				rt635.calc_arity(nullptr);
				sprawformtree ft634 = std::make_shared<raw_form_tree>(elem::NONE, rt635);
				sprawformtree ft633 = std::make_shared<raw_form_tree>(elem::NOT, ft634);
				sprawformtree ft615 = std::make_shared<raw_form_tree>(elem::AND, ft616, ft633);
				raw_rule rr636;
				rr636.h.push_back(rt614);
				rr636.set_prft(ft615);
				raw_term rt637;
				rt637.neg = false;
				rt637.extype = raw_term::REL;
				rt637.e.push_back(e566);
				rt637.e.push_back(e1);
				rt637.e.push_back(e213);
				rt637.e.push_back(e214);
				rt637.e.push_back(e62);
				rt637.e.push_back(e50);
				rt637.e.push_back(e3);
				rt637.calc_arity(nullptr);
				raw_term rt643;
				rt643.neg = false;
				rt643.extype = raw_term::REL;
				rt643.e.push_back(e557);
				rt643.e.push_back(e1);
				rt643.e.push_back(e213);
				rt643.e.push_back(e214);
				rt643.e.push_back(e198);
				rt643.e.push_back(e199);
				rt643.e.push_back(e62);
				rt643.e.push_back(e50);
				rt643.e.push_back(e3);
				rt643.calc_arity(nullptr);
				sprawformtree ft642 = std::make_shared<raw_form_tree>(elem::NONE, rt643);
				raw_term rt645;
				rt645.neg = false;
				rt645.extype = raw_term::REL;
				rt645.e.push_back(e156);
				rt645.e.push_back(e1);
				rt645.e.push_back(e198);
				rt645.e.push_back(e3);
				rt645.calc_arity(nullptr);
				sprawformtree ft644 = std::make_shared<raw_form_tree>(elem::NONE, rt645);
				sprawformtree ft641 = std::make_shared<raw_form_tree>(elem::AND, ft642, ft644);
				raw_term rt647;
				rt647.neg = false;
				rt647.extype = raw_term::REL;
				rt647.e.push_back(e156);
				rt647.e.push_back(e1);
				rt647.e.push_back(e199);
				rt647.e.push_back(e3);
				rt647.calc_arity(nullptr);
				sprawformtree ft646 = std::make_shared<raw_form_tree>(elem::NONE, rt647);
				sprawformtree ft640 = std::make_shared<raw_form_tree>(elem::AND, ft641, ft646);
				raw_term rt650;
				rt650.neg = false;
				rt650.extype = raw_term::REL;
				rt650.e.push_back(e566);
				rt650.e.push_back(e1);
				rt650.e.push_back(e213);
				rt650.e.push_back(e214);
				rt650.e.push_back(e62);
				rt650.e.push_back(e50);
				rt650.e.push_back(e3);
				rt650.calc_arity(nullptr);
				sprawformtree ft649 = std::make_shared<raw_form_tree>(elem::NONE, rt650);
				sprawformtree ft648 = std::make_shared<raw_form_tree>(elem::NOT, ft649);
				sprawformtree ft639 = std::make_shared<raw_form_tree>(elem::AND, ft640, ft648);
				raw_term rt653;
				rt653.neg = false;
				rt653.extype = raw_term::REL;
				rt653.e.push_back(e570);
				rt653.e.push_back(e1);
				rt653.e.push_back(e213);
				rt653.e.push_back(e214);
				rt653.e.push_back(e62);
				rt653.e.push_back(e50);
				rt653.e.push_back(e3);
				rt653.calc_arity(nullptr);
				sprawformtree ft652 = std::make_shared<raw_form_tree>(elem::NONE, rt653);
				sprawformtree ft651 = std::make_shared<raw_form_tree>(elem::NOT, ft652);
				sprawformtree ft638 = std::make_shared<raw_form_tree>(elem::AND, ft639, ft651);
				raw_rule rr654;
				rr654.h.push_back(rt637);
				rr654.set_prft(ft638);
				raw_term rt655;
				rt655.neg = true;
				rt655.extype = raw_term::REL;
				rt655.e.push_back(e557);
				rt655.e.push_back(e1);
				rt655.e.push_back(e213);
				rt655.e.push_back(e214);
				rt655.e.push_back(e215);
				rt655.e.push_back(e221);
				rt655.e.push_back(e62);
				rt655.e.push_back(e50);
				rt655.e.push_back(e3);
				rt655.calc_arity(nullptr);
				raw_term rt658;
				rt658.neg = false;
				rt658.extype = raw_term::REL;
				rt658.e.push_back(e566);
				rt658.e.push_back(e1);
				rt658.e.push_back(e213);
				rt658.e.push_back(e214);
				rt658.e.push_back(e62);
				rt658.e.push_back(e50);
				rt658.e.push_back(e3);
				rt658.calc_arity(nullptr);
				sprawformtree ft657 = std::make_shared<raw_form_tree>(elem::NONE, rt658);
				raw_term rt660;
				rt660.neg = false;
				rt660.extype = raw_term::REL;
				rt660.e.push_back(e570);
				rt660.e.push_back(e1);
				rt660.e.push_back(e213);
				rt660.e.push_back(e214);
				rt660.e.push_back(e62);
				rt660.e.push_back(e50);
				rt660.e.push_back(e3);
				rt660.calc_arity(nullptr);
				sprawformtree ft659 = std::make_shared<raw_form_tree>(elem::NONE, rt660);
				sprawformtree ft656 = std::make_shared<raw_form_tree>(elem::ALT, ft657, ft659);
				raw_rule rr661;
				rr661.h.push_back(rt655);
				rr661.set_prft(ft656);
				elem e662;
				e662.type = elem::SYM;
				e662.e = d.get_lexeme("IS_DICT_CONSISTENT0");
				raw_term rt663;
				rt663.neg = false;
				rt663.extype = raw_term::REL;
				rt663.e.push_back(e662);
				rt663.e.push_back(e1);
				rt663.e.push_back(e198);
				rt663.e.push_back(e199);
				rt663.e.push_back(e198);
				rt663.e.push_back(e199);
				rt663.e.push_back(e3);
				rt663.calc_arity(nullptr);
				elem e667;
				e667.type = elem::SYM;
				e667.e = d.get_lexeme("IS_DICT_CONSISTENT");
				raw_term rt668;
				rt668.neg = false;
				rt668.extype = raw_term::REL;
				rt668.e.push_back(e667);
				rt668.e.push_back(e1);
				rt668.e.push_back(e198);
				rt668.e.push_back(e199);
				rt668.e.push_back(e3);
				rt668.calc_arity(nullptr);
				sprawformtree ft666 = std::make_shared<raw_form_tree>(elem::NONE, rt668);
				elem e671;
				e671.type = elem::SYM;
				e671.e = d.get_lexeme("DICT_CONSISTENT");
				raw_term rt672;
				rt672.neg = false;
				rt672.extype = raw_term::REL;
				rt672.e.push_back(e671);
				rt672.e.push_back(e1);
				rt672.e.push_back(e198);
				rt672.e.push_back(e199);
				rt672.e.push_back(e3);
				rt672.calc_arity(nullptr);
				sprawformtree ft670 = std::make_shared<raw_form_tree>(elem::NONE, rt672);
				sprawformtree ft669 = std::make_shared<raw_form_tree>(elem::NOT, ft670);
				sprawformtree ft665 = std::make_shared<raw_form_tree>(elem::AND, ft666, ft669);
				sprawformtree ft675 = std::make_shared<raw_form_tree>(elem::VAR, e165);
				sprawformtree ft677 = std::make_shared<raw_form_tree>(elem::VAR, e42);
				elem e679;
				e679.type = elem::SYM;
				e679.e = d.get_lexeme("NOT_DICT_CONSISTENT");
				raw_term rt680;
				rt680.neg = false;
				rt680.extype = raw_term::REL;
				rt680.e.push_back(e679);
				rt680.e.push_back(e1);
				rt680.e.push_back(e213);
				rt680.e.push_back(e214);
				rt680.e.push_back(e165);
				rt680.e.push_back(e42);
				rt680.e.push_back(e3);
				rt680.calc_arity(nullptr);
				sprawformtree ft678 = std::make_shared<raw_form_tree>(elem::NONE, rt680);
				sprawformtree ft676 = std::make_shared<raw_form_tree>(elem::EXISTS, ft677, ft678);
				sprawformtree ft674 = std::make_shared<raw_form_tree>(elem::EXISTS, ft675, ft676);
				sprawformtree ft673 = std::make_shared<raw_form_tree>(elem::NOT, ft674);
				sprawformtree ft664 = std::make_shared<raw_form_tree>(elem::AND, ft665, ft673);
				raw_rule rr681;
				rr681.h.push_back(rt663);
				rr681.set_prft(ft664);
				raw_term rt682;
				rt682.neg = false;
				rt682.extype = raw_term::REL;
				rt682.e.push_back(e562);
				rt682.e.push_back(e1);
				rt682.e.push_back(e215);
				rt682.e.push_back(e221);
				rt682.e.push_back(e62);
				rt682.e.push_back(e50);
				rt682.e.push_back(e3);
				rt682.calc_arity(nullptr);
				elem e683;
				e683.type = elem::SYM;
				e683.e = d.get_lexeme("IS_DICT_CONSISTENT1");
				raw_term rt684;
				rt684.neg = false;
				rt684.extype = raw_term::REL;
				rt684.e.push_back(e683);
				rt684.e.push_back(e1);
				rt684.e.push_back(e213);
				rt684.e.push_back(e214);
				rt684.e.push_back(e198);
				rt684.e.push_back(e199);
				rt684.e.push_back(e3);
				rt684.calc_arity(nullptr);
				raw_term rt690;
				rt690.neg = false;
				rt690.extype = raw_term::REL;
				rt690.e.push_back(e662);
				rt690.e.push_back(e1);
				rt690.e.push_back(e213);
				rt690.e.push_back(e214);
				rt690.e.push_back(e198);
				rt690.e.push_back(e199);
				rt690.e.push_back(e3);
				rt690.calc_arity(nullptr);
				sprawformtree ft689 = std::make_shared<raw_form_tree>(elem::NONE, rt690);
				raw_term rt692;
				rt692.neg = false;
				rt692.extype = raw_term::REL;
				rt692.e.push_back(e156);
				rt692.e.push_back(e1);
				rt692.e.push_back(e198);
				rt692.e.push_back(e62);
				rt692.e.push_back(e215);
				rt692.e.push_back(e3);
				rt692.calc_arity(nullptr);
				sprawformtree ft691 = std::make_shared<raw_form_tree>(elem::NONE, rt692);
				sprawformtree ft688 = std::make_shared<raw_form_tree>(elem::AND, ft689, ft691);
				raw_term rt694;
				rt694.neg = false;
				rt694.extype = raw_term::REL;
				rt694.e.push_back(e156);
				rt694.e.push_back(e1);
				rt694.e.push_back(e199);
				rt694.e.push_back(e50);
				rt694.e.push_back(e221);
				rt694.e.push_back(e3);
				rt694.calc_arity(nullptr);
				sprawformtree ft693 = std::make_shared<raw_form_tree>(elem::NONE, rt694);
				sprawformtree ft687 = std::make_shared<raw_form_tree>(elem::AND, ft688, ft693);
				raw_term rt697;
				rt697.neg = false;
				rt697.extype = raw_term::REL;
				rt697.e.push_back(e671);
				rt697.e.push_back(e1);
				rt697.e.push_back(e213);
				rt697.e.push_back(e214);
				rt697.e.push_back(e3);
				rt697.calc_arity(nullptr);
				sprawformtree ft696 = std::make_shared<raw_form_tree>(elem::NONE, rt697);
				sprawformtree ft695 = std::make_shared<raw_form_tree>(elem::NOT, ft696);
				sprawformtree ft686 = std::make_shared<raw_form_tree>(elem::AND, ft687, ft695);
				sprawformtree ft700 = std::make_shared<raw_form_tree>(elem::VAR, e165);
				sprawformtree ft702 = std::make_shared<raw_form_tree>(elem::VAR, e42);
				raw_term rt704;
				rt704.neg = false;
				rt704.extype = raw_term::REL;
				rt704.e.push_back(e679);
				rt704.e.push_back(e1);
				rt704.e.push_back(e213);
				rt704.e.push_back(e214);
				rt704.e.push_back(e165);
				rt704.e.push_back(e42);
				rt704.e.push_back(e3);
				rt704.calc_arity(nullptr);
				sprawformtree ft703 = std::make_shared<raw_form_tree>(elem::NONE, rt704);
				sprawformtree ft701 = std::make_shared<raw_form_tree>(elem::EXISTS, ft702, ft703);
				sprawformtree ft699 = std::make_shared<raw_form_tree>(elem::EXISTS, ft700, ft701);
				sprawformtree ft698 = std::make_shared<raw_form_tree>(elem::NOT, ft699);
				sprawformtree ft685 = std::make_shared<raw_form_tree>(elem::AND, ft686, ft698);
				raw_rule rr705;
				rr705.h.push_back(rt682);
				rr705.h.push_back(rt684);
				rr705.set_prft(ft685);
				raw_term rt706;
				rt706.neg = false;
				rt706.extype = raw_term::REL;
				rt706.e.push_back(e662);
				rt706.e.push_back(e1);
				rt706.e.push_back(e213);
				rt706.e.push_back(e214);
				rt706.e.push_back(e215);
				rt706.e.push_back(e221);
				rt706.e.push_back(e3);
				rt706.calc_arity(nullptr);
				raw_term rt713;
				rt713.neg = false;
				rt713.extype = raw_term::REL;
				rt713.e.push_back(e566);
				rt713.e.push_back(e1);
				rt713.e.push_back(e215);
				rt713.e.push_back(e221);
				rt713.e.push_back(e62);
				rt713.e.push_back(e50);
				rt713.e.push_back(e3);
				rt713.calc_arity(nullptr);
				sprawformtree ft712 = std::make_shared<raw_form_tree>(elem::NONE, rt713);
				raw_term rt715;
				rt715.neg = false;
				rt715.extype = raw_term::REL;
				rt715.e.push_back(e683);
				rt715.e.push_back(e1);
				rt715.e.push_back(e213);
				rt715.e.push_back(e214);
				rt715.e.push_back(e198);
				rt715.e.push_back(e199);
				rt715.e.push_back(e3);
				rt715.calc_arity(nullptr);
				sprawformtree ft714 = std::make_shared<raw_form_tree>(elem::NONE, rt715);
				sprawformtree ft711 = std::make_shared<raw_form_tree>(elem::AND, ft712, ft714);
				raw_term rt717;
				rt717.neg = false;
				rt717.extype = raw_term::REL;
				rt717.e.push_back(e156);
				rt717.e.push_back(e1);
				rt717.e.push_back(e198);
				rt717.e.push_back(e62);
				rt717.e.push_back(e215);
				rt717.e.push_back(e3);
				rt717.calc_arity(nullptr);
				sprawformtree ft716 = std::make_shared<raw_form_tree>(elem::NONE, rt717);
				sprawformtree ft710 = std::make_shared<raw_form_tree>(elem::AND, ft711, ft716);
				raw_term rt719;
				rt719.neg = false;
				rt719.extype = raw_term::REL;
				rt719.e.push_back(e156);
				rt719.e.push_back(e1);
				rt719.e.push_back(e199);
				rt719.e.push_back(e50);
				rt719.e.push_back(e221);
				rt719.e.push_back(e3);
				rt719.calc_arity(nullptr);
				sprawformtree ft718 = std::make_shared<raw_form_tree>(elem::NONE, rt719);
				sprawformtree ft709 = std::make_shared<raw_form_tree>(elem::AND, ft710, ft718);
				raw_term rt722;
				rt722.neg = false;
				rt722.extype = raw_term::REL;
				rt722.e.push_back(e671);
				rt722.e.push_back(e1);
				rt722.e.push_back(e213);
				rt722.e.push_back(e214);
				rt722.e.push_back(e3);
				rt722.calc_arity(nullptr);
				sprawformtree ft721 = std::make_shared<raw_form_tree>(elem::NONE, rt722);
				sprawformtree ft720 = std::make_shared<raw_form_tree>(elem::NOT, ft721);
				sprawformtree ft708 = std::make_shared<raw_form_tree>(elem::AND, ft709, ft720);
				sprawformtree ft725 = std::make_shared<raw_form_tree>(elem::VAR, e165);
				sprawformtree ft727 = std::make_shared<raw_form_tree>(elem::VAR, e42);
				raw_term rt729;
				rt729.neg = false;
				rt729.extype = raw_term::REL;
				rt729.e.push_back(e679);
				rt729.e.push_back(e1);
				rt729.e.push_back(e213);
				rt729.e.push_back(e214);
				rt729.e.push_back(e165);
				rt729.e.push_back(e42);
				rt729.e.push_back(e3);
				rt729.calc_arity(nullptr);
				sprawformtree ft728 = std::make_shared<raw_form_tree>(elem::NONE, rt729);
				sprawformtree ft726 = std::make_shared<raw_form_tree>(elem::EXISTS, ft727, ft728);
				sprawformtree ft724 = std::make_shared<raw_form_tree>(elem::EXISTS, ft725, ft726);
				sprawformtree ft723 = std::make_shared<raw_form_tree>(elem::NOT, ft724);
				sprawformtree ft707 = std::make_shared<raw_form_tree>(elem::AND, ft708, ft723);
				raw_rule rr730;
				rr730.h.push_back(rt706);
				rr730.set_prft(ft707);
				raw_term rt731;
				rt731.neg = false;
				rt731.extype = raw_term::REL;
				rt731.e.push_back(e679);
				rt731.e.push_back(e1);
				rt731.e.push_back(e213);
				rt731.e.push_back(e214);
				rt731.e.push_back(e215);
				rt731.e.push_back(e221);
				rt731.e.push_back(e3);
				rt731.calc_arity(nullptr);
				raw_term rt738;
				rt738.neg = false;
				rt738.extype = raw_term::REL;
				rt738.e.push_back(e570);
				rt738.e.push_back(e1);
				rt738.e.push_back(e215);
				rt738.e.push_back(e221);
				rt738.e.push_back(e62);
				rt738.e.push_back(e50);
				rt738.e.push_back(e3);
				rt738.calc_arity(nullptr);
				sprawformtree ft737 = std::make_shared<raw_form_tree>(elem::NONE, rt738);
				raw_term rt740;
				rt740.neg = false;
				rt740.extype = raw_term::REL;
				rt740.e.push_back(e683);
				rt740.e.push_back(e1);
				rt740.e.push_back(e213);
				rt740.e.push_back(e214);
				rt740.e.push_back(e198);
				rt740.e.push_back(e199);
				rt740.e.push_back(e3);
				rt740.calc_arity(nullptr);
				sprawformtree ft739 = std::make_shared<raw_form_tree>(elem::NONE, rt740);
				sprawformtree ft736 = std::make_shared<raw_form_tree>(elem::AND, ft737, ft739);
				raw_term rt742;
				rt742.neg = false;
				rt742.extype = raw_term::REL;
				rt742.e.push_back(e156);
				rt742.e.push_back(e1);
				rt742.e.push_back(e198);
				rt742.e.push_back(e62);
				rt742.e.push_back(e215);
				rt742.e.push_back(e3);
				rt742.calc_arity(nullptr);
				sprawformtree ft741 = std::make_shared<raw_form_tree>(elem::NONE, rt742);
				sprawformtree ft735 = std::make_shared<raw_form_tree>(elem::AND, ft736, ft741);
				raw_term rt744;
				rt744.neg = false;
				rt744.extype = raw_term::REL;
				rt744.e.push_back(e156);
				rt744.e.push_back(e1);
				rt744.e.push_back(e199);
				rt744.e.push_back(e50);
				rt744.e.push_back(e221);
				rt744.e.push_back(e3);
				rt744.calc_arity(nullptr);
				sprawformtree ft743 = std::make_shared<raw_form_tree>(elem::NONE, rt744);
				sprawformtree ft734 = std::make_shared<raw_form_tree>(elem::AND, ft735, ft743);
				raw_term rt747;
				rt747.neg = false;
				rt747.extype = raw_term::REL;
				rt747.e.push_back(e671);
				rt747.e.push_back(e1);
				rt747.e.push_back(e213);
				rt747.e.push_back(e214);
				rt747.e.push_back(e3);
				rt747.calc_arity(nullptr);
				sprawformtree ft746 = std::make_shared<raw_form_tree>(elem::NONE, rt747);
				sprawformtree ft745 = std::make_shared<raw_form_tree>(elem::NOT, ft746);
				sprawformtree ft733 = std::make_shared<raw_form_tree>(elem::AND, ft734, ft745);
				sprawformtree ft750 = std::make_shared<raw_form_tree>(elem::VAR, e165);
				sprawformtree ft752 = std::make_shared<raw_form_tree>(elem::VAR, e42);
				raw_term rt754;
				rt754.neg = false;
				rt754.extype = raw_term::REL;
				rt754.e.push_back(e679);
				rt754.e.push_back(e1);
				rt754.e.push_back(e213);
				rt754.e.push_back(e214);
				rt754.e.push_back(e165);
				rt754.e.push_back(e42);
				rt754.e.push_back(e3);
				rt754.calc_arity(nullptr);
				sprawformtree ft753 = std::make_shared<raw_form_tree>(elem::NONE, rt754);
				sprawformtree ft751 = std::make_shared<raw_form_tree>(elem::EXISTS, ft752, ft753);
				sprawformtree ft749 = std::make_shared<raw_form_tree>(elem::EXISTS, ft750, ft751);
				sprawformtree ft748 = std::make_shared<raw_form_tree>(elem::NOT, ft749);
				sprawformtree ft732 = std::make_shared<raw_form_tree>(elem::AND, ft733, ft748);
				raw_rule rr755;
				rr755.h.push_back(rt731);
				rr755.set_prft(ft732);
				raw_term rt756;
				rt756.neg = false;
				rt756.extype = raw_term::REL;
				rt756.e.push_back(e671);
				rt756.e.push_back(e1);
				rt756.e.push_back(e213);
				rt756.e.push_back(e214);
				rt756.e.push_back(e3);
				rt756.calc_arity(nullptr);
				raw_term rt762;
				rt762.neg = false;
				rt762.extype = raw_term::REL;
				rt762.e.push_back(e662);
				rt762.e.push_back(e1);
				rt762.e.push_back(e213);
				rt762.e.push_back(e214);
				rt762.e.push_back(e198);
				rt762.e.push_back(e199);
				rt762.e.push_back(e3);
				rt762.calc_arity(nullptr);
				sprawformtree ft761 = std::make_shared<raw_form_tree>(elem::NONE, rt762);
				raw_term rt764;
				rt764.neg = false;
				rt764.extype = raw_term::REL;
				rt764.e.push_back(e156);
				rt764.e.push_back(e1);
				rt764.e.push_back(e198);
				rt764.e.push_back(e3);
				rt764.calc_arity(nullptr);
				sprawformtree ft763 = std::make_shared<raw_form_tree>(elem::NONE, rt764);
				sprawformtree ft760 = std::make_shared<raw_form_tree>(elem::AND, ft761, ft763);
				raw_term rt766;
				rt766.neg = false;
				rt766.extype = raw_term::REL;
				rt766.e.push_back(e156);
				rt766.e.push_back(e1);
				rt766.e.push_back(e199);
				rt766.e.push_back(e3);
				rt766.calc_arity(nullptr);
				sprawformtree ft765 = std::make_shared<raw_form_tree>(elem::NONE, rt766);
				sprawformtree ft759 = std::make_shared<raw_form_tree>(elem::AND, ft760, ft765);
				raw_term rt769;
				rt769.neg = false;
				rt769.extype = raw_term::REL;
				rt769.e.push_back(e671);
				rt769.e.push_back(e1);
				rt769.e.push_back(e213);
				rt769.e.push_back(e214);
				rt769.e.push_back(e3);
				rt769.calc_arity(nullptr);
				sprawformtree ft768 = std::make_shared<raw_form_tree>(elem::NONE, rt769);
				sprawformtree ft767 = std::make_shared<raw_form_tree>(elem::NOT, ft768);
				sprawformtree ft758 = std::make_shared<raw_form_tree>(elem::AND, ft759, ft767);
				sprawformtree ft772 = std::make_shared<raw_form_tree>(elem::VAR, e165);
				sprawformtree ft774 = std::make_shared<raw_form_tree>(elem::VAR, e42);
				raw_term rt776;
				rt776.neg = false;
				rt776.extype = raw_term::REL;
				rt776.e.push_back(e679);
				rt776.e.push_back(e1);
				rt776.e.push_back(e213);
				rt776.e.push_back(e214);
				rt776.e.push_back(e165);
				rt776.e.push_back(e42);
				rt776.e.push_back(e3);
				rt776.calc_arity(nullptr);
				sprawformtree ft775 = std::make_shared<raw_form_tree>(elem::NONE, rt776);
				sprawformtree ft773 = std::make_shared<raw_form_tree>(elem::EXISTS, ft774, ft775);
				sprawformtree ft771 = std::make_shared<raw_form_tree>(elem::EXISTS, ft772, ft773);
				sprawformtree ft770 = std::make_shared<raw_form_tree>(elem::NOT, ft771);
				sprawformtree ft757 = std::make_shared<raw_form_tree>(elem::AND, ft758, ft770);
				raw_rule rr777;
				rr777.h.push_back(rt756);
				rr777.set_prft(ft757);
				raw_term rt778;
				rt778.neg = true;
				rt778.extype = raw_term::REL;
				rt778.e.push_back(e662);
				rt778.e.push_back(e1);
				rt778.e.push_back(e213);
				rt778.e.push_back(e214);
				rt778.e.push_back(e198);
				rt778.e.push_back(e199);
				rt778.e.push_back(e3);
				rt778.calc_arity(nullptr);
				raw_term rt779;
				rt779.neg = true;
				rt779.extype = raw_term::REL;
				rt779.e.push_back(e683);
				rt779.e.push_back(e1);
				rt779.e.push_back(e213);
				rt779.e.push_back(e214);
				rt779.e.push_back(e198);
				rt779.e.push_back(e199);
				rt779.e.push_back(e3);
				rt779.calc_arity(nullptr);
				raw_term rt782;
				rt782.neg = false;
				rt782.extype = raw_term::REL;
				rt782.e.push_back(e671);
				rt782.e.push_back(e1);
				rt782.e.push_back(e213);
				rt782.e.push_back(e214);
				rt782.e.push_back(e3);
				rt782.calc_arity(nullptr);
				sprawformtree ft781 = std::make_shared<raw_form_tree>(elem::NONE, rt782);
				elem e784;
				e784.type = elem::VAR;
				e784.e = d.get_lexeme("?axs");
				elem e785;
				e785.type = elem::VAR;
				e785.e = d.get_lexeme("?ays");
				raw_term rt786;
				rt786.neg = false;
				rt786.extype = raw_term::REL;
				rt786.e.push_back(e679);
				rt786.e.push_back(e1);
				rt786.e.push_back(e213);
				rt786.e.push_back(e214);
				rt786.e.push_back(e784);
				rt786.e.push_back(e785);
				rt786.e.push_back(e3);
				rt786.calc_arity(nullptr);
				sprawformtree ft783 = std::make_shared<raw_form_tree>(elem::NONE, rt786);
				sprawformtree ft780 = std::make_shared<raw_form_tree>(elem::ALT, ft781, ft783);
				raw_rule rr787;
				rr787.h.push_back(rt778);
				rr787.h.push_back(rt779);
				rr787.set_prft(ft780);
				elem e788;
				e788.type = elem::SYM;
				e788.e = d.get_lexeme("DO_SELECTION0");
				raw_term rt789;
				rt789.neg = false;
				rt789.extype = raw_term::REL;
				rt789.e.push_back(e788);
				rt789.e.push_back(e1);
				rt789.e.push_back(e239);
				rt789.e.push_back(e254);
				rt789.e.push_back(e239);
				rt789.e.push_back(e254);
				rt789.e.push_back(e208);
				rt789.e.push_back(e3);
				rt789.calc_arity(nullptr);
				elem e793;
				e793.type = elem::SYM;
				e793.e = d.get_lexeme("DO_SELECTION");
				raw_term rt794;
				rt794.neg = false;
				rt794.extype = raw_term::REL;
				rt794.e.push_back(e793);
				rt794.e.push_back(e1);
				rt794.e.push_back(e239);
				rt794.e.push_back(e254);
				rt794.e.push_back(e3);
				rt794.calc_arity(nullptr);
				sprawformtree ft792 = std::make_shared<raw_form_tree>(elem::NONE, rt794);
				raw_term rt796;
				rt796.neg = false;
				rt796.extype = raw_term::REL;
				rt796.e.push_back(e156);
				rt796.e.push_back(e1);
				rt796.e.push_back(e208);
				rt796.e.push_back(e3);
				rt796.calc_arity(nullptr);
				sprawformtree ft795 = std::make_shared<raw_form_tree>(elem::NONE, rt796);
				sprawformtree ft791 = std::make_shared<raw_form_tree>(elem::AND, ft792, ft795);
				sprawformtree ft799 = std::make_shared<raw_form_tree>(elem::VAR, e165);
				elem e801;
				e801.type = elem::SYM;
				e801.e = d.get_lexeme("SELECTION");
				raw_term rt802;
				rt802.neg = false;
				rt802.extype = raw_term::REL;
				rt802.e.push_back(e801);
				rt802.e.push_back(e1);
				rt802.e.push_back(e239);
				rt802.e.push_back(e254);
				rt802.e.push_back(e165);
				rt802.e.push_back(e3);
				rt802.calc_arity(nullptr);
				sprawformtree ft800 = std::make_shared<raw_form_tree>(elem::NONE, rt802);
				sprawformtree ft798 = std::make_shared<raw_form_tree>(elem::EXISTS, ft799, ft800);
				sprawformtree ft797 = std::make_shared<raw_form_tree>(elem::NOT, ft798);
				sprawformtree ft790 = std::make_shared<raw_form_tree>(elem::AND, ft791, ft797);
				raw_rule rr803;
				rr803.h.push_back(rt789);
				rr803.set_prft(ft790);
				elem e804;
				e804.type = elem::VAR;
				e804.e = d.get_lexeme("?oas");
				elem e805;
				e805.type = elem::VAR;
				e805.e = d.get_lexeme("?bs_tl");
				raw_term rt806;
				rt806.neg = false;
				rt806.extype = raw_term::REL;
				rt806.e.push_back(e788);
				rt806.e.push_back(e1);
				rt806.e.push_back(e804);
				rt806.e.push_back(e269);
				rt806.e.push_back(e276);
				rt806.e.push_back(e805);
				rt806.e.push_back(e208);
				rt806.e.push_back(e3);
				rt806.calc_arity(nullptr);
				elem e812;
				e812.type = elem::VAR;
				e812.e = d.get_lexeme("?cs_tl");
				raw_term rt813;
				rt813.neg = false;
				rt813.extype = raw_term::REL;
				rt813.e.push_back(e788);
				rt813.e.push_back(e1);
				rt813.e.push_back(e804);
				rt813.e.push_back(e269);
				rt813.e.push_back(e239);
				rt813.e.push_back(e254);
				rt813.e.push_back(e812);
				rt813.e.push_back(e3);
				rt813.calc_arity(nullptr);
				sprawformtree ft811 = std::make_shared<raw_form_tree>(elem::NONE, rt813);
				raw_term rt815;
				rt815.neg = false;
				rt815.extype = raw_term::REL;
				rt815.e.push_back(e156);
				rt815.e.push_back(e1);
				rt815.e.push_back(e239);
				rt815.e.push_back(e275);
				rt815.e.push_back(e276);
				rt815.e.push_back(e3);
				rt815.calc_arity(nullptr);
				sprawformtree ft814 = std::make_shared<raw_form_tree>(elem::NONE, rt815);
				sprawformtree ft810 = std::make_shared<raw_form_tree>(elem::AND, ft811, ft814);
				elem e817;
				e817.type = elem::NUM;
				e817.num = 1;
				raw_term rt818;
				rt818.neg = false;
				rt818.extype = raw_term::REL;
				rt818.e.push_back(e156);
				rt818.e.push_back(e1);
				rt818.e.push_back(e254);
				rt818.e.push_back(e817);
				rt818.e.push_back(e805);
				rt818.e.push_back(e3);
				rt818.calc_arity(nullptr);
				sprawformtree ft816 = std::make_shared<raw_form_tree>(elem::NONE, rt818);
				sprawformtree ft809 = std::make_shared<raw_form_tree>(elem::AND, ft810, ft816);
				raw_term rt820;
				rt820.neg = false;
				rt820.extype = raw_term::REL;
				rt820.e.push_back(e156);
				rt820.e.push_back(e1);
				rt820.e.push_back(e208);
				rt820.e.push_back(e275);
				rt820.e.push_back(e812);
				rt820.e.push_back(e3);
				rt820.calc_arity(nullptr);
				sprawformtree ft819 = std::make_shared<raw_form_tree>(elem::NONE, rt820);
				sprawformtree ft808 = std::make_shared<raw_form_tree>(elem::AND, ft809, ft819);
				sprawformtree ft823 = std::make_shared<raw_form_tree>(elem::VAR, e165);
				raw_term rt825;
				rt825.neg = false;
				rt825.extype = raw_term::REL;
				rt825.e.push_back(e801);
				rt825.e.push_back(e1);
				rt825.e.push_back(e804);
				rt825.e.push_back(e269);
				rt825.e.push_back(e165);
				rt825.e.push_back(e3);
				rt825.calc_arity(nullptr);
				sprawformtree ft824 = std::make_shared<raw_form_tree>(elem::NONE, rt825);
				sprawformtree ft822 = std::make_shared<raw_form_tree>(elem::EXISTS, ft823, ft824);
				sprawformtree ft821 = std::make_shared<raw_form_tree>(elem::NOT, ft822);
				sprawformtree ft807 = std::make_shared<raw_form_tree>(elem::AND, ft808, ft821);
				raw_rule rr826;
				rr826.h.push_back(rt806);
				rr826.set_prft(ft807);
				raw_term rt827;
				rt827.neg = false;
				rt827.extype = raw_term::REL;
				rt827.e.push_back(e788);
				rt827.e.push_back(e1);
				rt827.e.push_back(e804);
				rt827.e.push_back(e269);
				rt827.e.push_back(e276);
				rt827.e.push_back(e805);
				rt827.e.push_back(e208);
				rt827.e.push_back(e3);
				rt827.calc_arity(nullptr);
				raw_term rt832;
				rt832.neg = false;
				rt832.extype = raw_term::REL;
				rt832.e.push_back(e788);
				rt832.e.push_back(e1);
				rt832.e.push_back(e804);
				rt832.e.push_back(e269);
				rt832.e.push_back(e239);
				rt832.e.push_back(e254);
				rt832.e.push_back(e208);
				rt832.e.push_back(e3);
				rt832.calc_arity(nullptr);
				sprawformtree ft831 = std::make_shared<raw_form_tree>(elem::NONE, rt832);
				raw_term rt834;
				rt834.neg = false;
				rt834.extype = raw_term::REL;
				rt834.e.push_back(e156);
				rt834.e.push_back(e1);
				rt834.e.push_back(e239);
				rt834.e.push_back(e275);
				rt834.e.push_back(e276);
				rt834.e.push_back(e3);
				rt834.calc_arity(nullptr);
				sprawformtree ft833 = std::make_shared<raw_form_tree>(elem::NONE, rt834);
				sprawformtree ft830 = std::make_shared<raw_form_tree>(elem::AND, ft831, ft833);
				raw_term rt836;
				rt836.neg = false;
				rt836.extype = raw_term::REL;
				rt836.e.push_back(e156);
				rt836.e.push_back(e1);
				rt836.e.push_back(e254);
				rt836.e.push_back(e111);
				rt836.e.push_back(e805);
				rt836.e.push_back(e3);
				rt836.calc_arity(nullptr);
				sprawformtree ft835 = std::make_shared<raw_form_tree>(elem::NONE, rt836);
				sprawformtree ft829 = std::make_shared<raw_form_tree>(elem::AND, ft830, ft835);
				sprawformtree ft839 = std::make_shared<raw_form_tree>(elem::VAR, e165);
				raw_term rt841;
				rt841.neg = false;
				rt841.extype = raw_term::REL;
				rt841.e.push_back(e801);
				rt841.e.push_back(e1);
				rt841.e.push_back(e804);
				rt841.e.push_back(e269);
				rt841.e.push_back(e165);
				rt841.e.push_back(e3);
				rt841.calc_arity(nullptr);
				sprawformtree ft840 = std::make_shared<raw_form_tree>(elem::NONE, rt841);
				sprawformtree ft838 = std::make_shared<raw_form_tree>(elem::EXISTS, ft839, ft840);
				sprawformtree ft837 = std::make_shared<raw_form_tree>(elem::NOT, ft838);
				sprawformtree ft828 = std::make_shared<raw_form_tree>(elem::AND, ft829, ft837);
				raw_rule rr842;
				rr842.h.push_back(rt827);
				rr842.set_prft(ft828);
				raw_term rt843;
				rt843.neg = false;
				rt843.extype = raw_term::REL;
				rt843.e.push_back(e253);
				rt843.e.push_back(e1);
				rt843.e.push_back(e208);
				rt843.e.push_back(e3);
				rt843.calc_arity(nullptr);
				elem e844;
				e844.type = elem::SYM;
				e844.e = d.get_lexeme("DO_SELECTION1");
				raw_term rt845;
				rt845.neg = false;
				rt845.extype = raw_term::REL;
				rt845.e.push_back(e844);
				rt845.e.push_back(e1);
				rt845.e.push_back(e804);
				rt845.e.push_back(e269);
				rt845.e.push_back(e208);
				rt845.e.push_back(e3);
				rt845.calc_arity(nullptr);
				raw_term rt850;
				rt850.neg = false;
				rt850.extype = raw_term::REL;
				rt850.e.push_back(e788);
				rt850.e.push_back(e1);
				rt850.e.push_back(e804);
				rt850.e.push_back(e269);
				rt850.e.push_back(e239);
				rt850.e.push_back(e254);
				rt850.e.push_back(e208);
				rt850.e.push_back(e3);
				rt850.calc_arity(nullptr);
				sprawformtree ft849 = std::make_shared<raw_form_tree>(elem::NONE, rt850);
				raw_term rt852;
				rt852.neg = false;
				rt852.extype = raw_term::REL;
				rt852.e.push_back(e156);
				rt852.e.push_back(e1);
				rt852.e.push_back(e239);
				rt852.e.push_back(e3);
				rt852.calc_arity(nullptr);
				sprawformtree ft851 = std::make_shared<raw_form_tree>(elem::NONE, rt852);
				sprawformtree ft848 = std::make_shared<raw_form_tree>(elem::AND, ft849, ft851);
				raw_term rt854;
				rt854.neg = false;
				rt854.extype = raw_term::REL;
				rt854.e.push_back(e156);
				rt854.e.push_back(e1);
				rt854.e.push_back(e254);
				rt854.e.push_back(e3);
				rt854.calc_arity(nullptr);
				sprawformtree ft853 = std::make_shared<raw_form_tree>(elem::NONE, rt854);
				sprawformtree ft847 = std::make_shared<raw_form_tree>(elem::AND, ft848, ft853);
				sprawformtree ft857 = std::make_shared<raw_form_tree>(elem::VAR, e165);
				raw_term rt859;
				rt859.neg = false;
				rt859.extype = raw_term::REL;
				rt859.e.push_back(e801);
				rt859.e.push_back(e1);
				rt859.e.push_back(e804);
				rt859.e.push_back(e269);
				rt859.e.push_back(e165);
				rt859.e.push_back(e3);
				rt859.calc_arity(nullptr);
				sprawformtree ft858 = std::make_shared<raw_form_tree>(elem::NONE, rt859);
				sprawformtree ft856 = std::make_shared<raw_form_tree>(elem::EXISTS, ft857, ft858);
				sprawformtree ft855 = std::make_shared<raw_form_tree>(elem::NOT, ft856);
				sprawformtree ft846 = std::make_shared<raw_form_tree>(elem::AND, ft847, ft855);
				raw_rule rr860;
				rr860.h.push_back(rt843);
				rr860.h.push_back(rt845);
				rr860.set_prft(ft846);
				elem e861;
				e861.type = elem::VAR;
				e861.e = d.get_lexeme("?ds");
				raw_term rt862;
				rt862.neg = false;
				rt862.extype = raw_term::REL;
				rt862.e.push_back(e801);
				rt862.e.push_back(e1);
				rt862.e.push_back(e239);
				rt862.e.push_back(e861);
				rt862.e.push_back(e254);
				rt862.e.push_back(e3);
				rt862.calc_arity(nullptr);
				raw_term rt865;
				rt865.neg = false;
				rt865.extype = raw_term::REL;
				rt865.e.push_back(e844);
				rt865.e.push_back(e1);
				rt865.e.push_back(e239);
				rt865.e.push_back(e861);
				rt865.e.push_back(e208);
				rt865.e.push_back(e3);
				rt865.calc_arity(nullptr);
				sprawformtree ft864 = std::make_shared<raw_form_tree>(elem::NONE, rt865);
				raw_term rt867;
				rt867.neg = false;
				rt867.extype = raw_term::REL;
				rt867.e.push_back(e266);
				rt867.e.push_back(e1);
				rt867.e.push_back(e208);
				rt867.e.push_back(e254);
				rt867.e.push_back(e3);
				rt867.calc_arity(nullptr);
				sprawformtree ft866 = std::make_shared<raw_form_tree>(elem::NONE, rt867);
				sprawformtree ft863 = std::make_shared<raw_form_tree>(elem::AND, ft864, ft866);
				raw_rule rr868;
				rr868.h.push_back(rt862);
				rr868.set_prft(ft863);
				raw_term rt869;
				rt869.neg = true;
				rt869.extype = raw_term::REL;
				rt869.e.push_back(e788);
				rt869.e.push_back(e1);
				rt869.e.push_back(e804);
				rt869.e.push_back(e269);
				rt869.e.push_back(e239);
				rt869.e.push_back(e254);
				rt869.e.push_back(e208);
				rt869.e.push_back(e3);
				rt869.calc_arity(nullptr);
				raw_term rt870;
				rt870.neg = true;
				rt870.extype = raw_term::REL;
				rt870.e.push_back(e844);
				rt870.e.push_back(e1);
				rt870.e.push_back(e804);
				rt870.e.push_back(e269);
				rt870.e.push_back(e208);
				rt870.e.push_back(e3);
				rt870.calc_arity(nullptr);
				raw_term rt872;
				rt872.neg = false;
				rt872.extype = raw_term::REL;
				rt872.e.push_back(e801);
				rt872.e.push_back(e1);
				rt872.e.push_back(e804);
				rt872.e.push_back(e269);
				rt872.e.push_back(e165);
				rt872.e.push_back(e3);
				rt872.calc_arity(nullptr);
				sprawformtree ft871 = std::make_shared<raw_form_tree>(elem::NONE, rt872);
				raw_rule rr873;
				rr873.h.push_back(rt869);
				rr873.h.push_back(rt870);
				rr873.set_prft(ft871);
				elem e874;
				e874.type = elem::SYM;
				e874.e = d.get_lexeme("DO_DESELECTION0");
				raw_term rt875;
				rt875.neg = false;
				rt875.extype = raw_term::REL;
				rt875.e.push_back(e874);
				rt875.e.push_back(e1);
				rt875.e.push_back(e239);
				rt875.e.push_back(e254);
				rt875.e.push_back(e239);
				rt875.e.push_back(e254);
				rt875.e.push_back(e208);
				rt875.e.push_back(e3);
				rt875.calc_arity(nullptr);
				elem e879;
				e879.type = elem::SYM;
				e879.e = d.get_lexeme("DO_DESELECTION");
				raw_term rt880;
				rt880.neg = false;
				rt880.extype = raw_term::REL;
				rt880.e.push_back(e879);
				rt880.e.push_back(e1);
				rt880.e.push_back(e239);
				rt880.e.push_back(e254);
				rt880.e.push_back(e3);
				rt880.calc_arity(nullptr);
				sprawformtree ft878 = std::make_shared<raw_form_tree>(elem::NONE, rt880);
				raw_term rt882;
				rt882.neg = false;
				rt882.extype = raw_term::REL;
				rt882.e.push_back(e156);
				rt882.e.push_back(e1);
				rt882.e.push_back(e208);
				rt882.e.push_back(e3);
				rt882.calc_arity(nullptr);
				sprawformtree ft881 = std::make_shared<raw_form_tree>(elem::NONE, rt882);
				sprawformtree ft877 = std::make_shared<raw_form_tree>(elem::AND, ft878, ft881);
				sprawformtree ft885 = std::make_shared<raw_form_tree>(elem::VAR, e165);
				elem e887;
				e887.type = elem::SYM;
				e887.e = d.get_lexeme("DESELECTION");
				raw_term rt888;
				rt888.neg = false;
				rt888.extype = raw_term::REL;
				rt888.e.push_back(e887);
				rt888.e.push_back(e1);
				rt888.e.push_back(e239);
				rt888.e.push_back(e254);
				rt888.e.push_back(e165);
				rt888.e.push_back(e3);
				rt888.calc_arity(nullptr);
				sprawformtree ft886 = std::make_shared<raw_form_tree>(elem::NONE, rt888);
				sprawformtree ft884 = std::make_shared<raw_form_tree>(elem::EXISTS, ft885, ft886);
				sprawformtree ft883 = std::make_shared<raw_form_tree>(elem::NOT, ft884);
				sprawformtree ft876 = std::make_shared<raw_form_tree>(elem::AND, ft877, ft883);
				raw_rule rr889;
				rr889.h.push_back(rt875);
				rr889.set_prft(ft876);
				raw_term rt890;
				rt890.neg = false;
				rt890.extype = raw_term::REL;
				rt890.e.push_back(e874);
				rt890.e.push_back(e1);
				rt890.e.push_back(e804);
				rt890.e.push_back(e269);
				rt890.e.push_back(e276);
				rt890.e.push_back(e805);
				rt890.e.push_back(e208);
				rt890.e.push_back(e3);
				rt890.calc_arity(nullptr);
				raw_term rt896;
				rt896.neg = false;
				rt896.extype = raw_term::REL;
				rt896.e.push_back(e874);
				rt896.e.push_back(e1);
				rt896.e.push_back(e804);
				rt896.e.push_back(e269);
				rt896.e.push_back(e239);
				rt896.e.push_back(e254);
				rt896.e.push_back(e812);
				rt896.e.push_back(e3);
				rt896.calc_arity(nullptr);
				sprawformtree ft895 = std::make_shared<raw_form_tree>(elem::NONE, rt896);
				raw_term rt898;
				rt898.neg = false;
				rt898.extype = raw_term::REL;
				rt898.e.push_back(e156);
				rt898.e.push_back(e1);
				rt898.e.push_back(e239);
				rt898.e.push_back(e275);
				rt898.e.push_back(e276);
				rt898.e.push_back(e3);
				rt898.calc_arity(nullptr);
				sprawformtree ft897 = std::make_shared<raw_form_tree>(elem::NONE, rt898);
				sprawformtree ft894 = std::make_shared<raw_form_tree>(elem::AND, ft895, ft897);
				raw_term rt900;
				rt900.neg = false;
				rt900.extype = raw_term::REL;
				rt900.e.push_back(e156);
				rt900.e.push_back(e1);
				rt900.e.push_back(e254);
				rt900.e.push_back(e111);
				rt900.e.push_back(e805);
				rt900.e.push_back(e3);
				rt900.calc_arity(nullptr);
				sprawformtree ft899 = std::make_shared<raw_form_tree>(elem::NONE, rt900);
				sprawformtree ft893 = std::make_shared<raw_form_tree>(elem::AND, ft894, ft899);
				raw_term rt902;
				rt902.neg = false;
				rt902.extype = raw_term::REL;
				rt902.e.push_back(e156);
				rt902.e.push_back(e1);
				rt902.e.push_back(e208);
				rt902.e.push_back(e275);
				rt902.e.push_back(e812);
				rt902.e.push_back(e3);
				rt902.calc_arity(nullptr);
				sprawformtree ft901 = std::make_shared<raw_form_tree>(elem::NONE, rt902);
				sprawformtree ft892 = std::make_shared<raw_form_tree>(elem::AND, ft893, ft901);
				sprawformtree ft905 = std::make_shared<raw_form_tree>(elem::VAR, e165);
				raw_term rt907;
				rt907.neg = false;
				rt907.extype = raw_term::REL;
				rt907.e.push_back(e887);
				rt907.e.push_back(e1);
				rt907.e.push_back(e804);
				rt907.e.push_back(e269);
				rt907.e.push_back(e165);
				rt907.e.push_back(e3);
				rt907.calc_arity(nullptr);
				sprawformtree ft906 = std::make_shared<raw_form_tree>(elem::NONE, rt907);
				sprawformtree ft904 = std::make_shared<raw_form_tree>(elem::EXISTS, ft905, ft906);
				sprawformtree ft903 = std::make_shared<raw_form_tree>(elem::NOT, ft904);
				sprawformtree ft891 = std::make_shared<raw_form_tree>(elem::AND, ft892, ft903);
				raw_rule rr908;
				rr908.h.push_back(rt890);
				rr908.set_prft(ft891);
				raw_term rt909;
				rt909.neg = false;
				rt909.extype = raw_term::REL;
				rt909.e.push_back(e874);
				rt909.e.push_back(e1);
				rt909.e.push_back(e804);
				rt909.e.push_back(e269);
				rt909.e.push_back(e276);
				rt909.e.push_back(e805);
				rt909.e.push_back(e208);
				rt909.e.push_back(e3);
				rt909.calc_arity(nullptr);
				raw_term rt914;
				rt914.neg = false;
				rt914.extype = raw_term::REL;
				rt914.e.push_back(e874);
				rt914.e.push_back(e1);
				rt914.e.push_back(e804);
				rt914.e.push_back(e269);
				rt914.e.push_back(e239);
				rt914.e.push_back(e254);
				rt914.e.push_back(e208);
				rt914.e.push_back(e3);
				rt914.calc_arity(nullptr);
				sprawformtree ft913 = std::make_shared<raw_form_tree>(elem::NONE, rt914);
				raw_term rt916;
				rt916.neg = false;
				rt916.extype = raw_term::REL;
				rt916.e.push_back(e156);
				rt916.e.push_back(e1);
				rt916.e.push_back(e239);
				rt916.e.push_back(e275);
				rt916.e.push_back(e276);
				rt916.e.push_back(e3);
				rt916.calc_arity(nullptr);
				sprawformtree ft915 = std::make_shared<raw_form_tree>(elem::NONE, rt916);
				sprawformtree ft912 = std::make_shared<raw_form_tree>(elem::AND, ft913, ft915);
				raw_term rt918;
				rt918.neg = false;
				rt918.extype = raw_term::REL;
				rt918.e.push_back(e156);
				rt918.e.push_back(e1);
				rt918.e.push_back(e254);
				rt918.e.push_back(e817);
				rt918.e.push_back(e805);
				rt918.e.push_back(e3);
				rt918.calc_arity(nullptr);
				sprawformtree ft917 = std::make_shared<raw_form_tree>(elem::NONE, rt918);
				sprawformtree ft911 = std::make_shared<raw_form_tree>(elem::AND, ft912, ft917);
				sprawformtree ft921 = std::make_shared<raw_form_tree>(elem::VAR, e165);
				raw_term rt923;
				rt923.neg = false;
				rt923.extype = raw_term::REL;
				rt923.e.push_back(e887);
				rt923.e.push_back(e1);
				rt923.e.push_back(e804);
				rt923.e.push_back(e269);
				rt923.e.push_back(e165);
				rt923.e.push_back(e3);
				rt923.calc_arity(nullptr);
				sprawformtree ft922 = std::make_shared<raw_form_tree>(elem::NONE, rt923);
				sprawformtree ft920 = std::make_shared<raw_form_tree>(elem::EXISTS, ft921, ft922);
				sprawformtree ft919 = std::make_shared<raw_form_tree>(elem::NOT, ft920);
				sprawformtree ft910 = std::make_shared<raw_form_tree>(elem::AND, ft911, ft919);
				raw_rule rr924;
				rr924.h.push_back(rt909);
				rr924.set_prft(ft910);
				raw_term rt925;
				rt925.neg = false;
				rt925.extype = raw_term::REL;
				rt925.e.push_back(e253);
				rt925.e.push_back(e1);
				rt925.e.push_back(e208);
				rt925.e.push_back(e3);
				rt925.calc_arity(nullptr);
				elem e926;
				e926.type = elem::SYM;
				e926.e = d.get_lexeme("DO_DESELECTION1");
				raw_term rt927;
				rt927.neg = false;
				rt927.extype = raw_term::REL;
				rt927.e.push_back(e926);
				rt927.e.push_back(e1);
				rt927.e.push_back(e804);
				rt927.e.push_back(e269);
				rt927.e.push_back(e208);
				rt927.e.push_back(e3);
				rt927.calc_arity(nullptr);
				raw_term rt932;
				rt932.neg = false;
				rt932.extype = raw_term::REL;
				rt932.e.push_back(e874);
				rt932.e.push_back(e1);
				rt932.e.push_back(e804);
				rt932.e.push_back(e269);
				rt932.e.push_back(e239);
				rt932.e.push_back(e254);
				rt932.e.push_back(e208);
				rt932.e.push_back(e3);
				rt932.calc_arity(nullptr);
				sprawformtree ft931 = std::make_shared<raw_form_tree>(elem::NONE, rt932);
				raw_term rt934;
				rt934.neg = false;
				rt934.extype = raw_term::REL;
				rt934.e.push_back(e156);
				rt934.e.push_back(e1);
				rt934.e.push_back(e239);
				rt934.e.push_back(e3);
				rt934.calc_arity(nullptr);
				sprawformtree ft933 = std::make_shared<raw_form_tree>(elem::NONE, rt934);
				sprawformtree ft930 = std::make_shared<raw_form_tree>(elem::AND, ft931, ft933);
				raw_term rt936;
				rt936.neg = false;
				rt936.extype = raw_term::REL;
				rt936.e.push_back(e156);
				rt936.e.push_back(e1);
				rt936.e.push_back(e254);
				rt936.e.push_back(e3);
				rt936.calc_arity(nullptr);
				sprawformtree ft935 = std::make_shared<raw_form_tree>(elem::NONE, rt936);
				sprawformtree ft929 = std::make_shared<raw_form_tree>(elem::AND, ft930, ft935);
				sprawformtree ft939 = std::make_shared<raw_form_tree>(elem::VAR, e165);
				raw_term rt941;
				rt941.neg = false;
				rt941.extype = raw_term::REL;
				rt941.e.push_back(e887);
				rt941.e.push_back(e1);
				rt941.e.push_back(e804);
				rt941.e.push_back(e269);
				rt941.e.push_back(e165);
				rt941.e.push_back(e3);
				rt941.calc_arity(nullptr);
				sprawformtree ft940 = std::make_shared<raw_form_tree>(elem::NONE, rt941);
				sprawformtree ft938 = std::make_shared<raw_form_tree>(elem::EXISTS, ft939, ft940);
				sprawformtree ft937 = std::make_shared<raw_form_tree>(elem::NOT, ft938);
				sprawformtree ft928 = std::make_shared<raw_form_tree>(elem::AND, ft929, ft937);
				raw_rule rr942;
				rr942.h.push_back(rt925);
				rr942.h.push_back(rt927);
				rr942.set_prft(ft928);
				raw_term rt943;
				rt943.neg = false;
				rt943.extype = raw_term::REL;
				rt943.e.push_back(e887);
				rt943.e.push_back(e1);
				rt943.e.push_back(e239);
				rt943.e.push_back(e861);
				rt943.e.push_back(e254);
				rt943.e.push_back(e3);
				rt943.calc_arity(nullptr);
				raw_term rt946;
				rt946.neg = false;
				rt946.extype = raw_term::REL;
				rt946.e.push_back(e926);
				rt946.e.push_back(e1);
				rt946.e.push_back(e239);
				rt946.e.push_back(e861);
				rt946.e.push_back(e208);
				rt946.e.push_back(e3);
				rt946.calc_arity(nullptr);
				sprawformtree ft945 = std::make_shared<raw_form_tree>(elem::NONE, rt946);
				raw_term rt948;
				rt948.neg = false;
				rt948.extype = raw_term::REL;
				rt948.e.push_back(e266);
				rt948.e.push_back(e1);
				rt948.e.push_back(e208);
				rt948.e.push_back(e254);
				rt948.e.push_back(e3);
				rt948.calc_arity(nullptr);
				sprawformtree ft947 = std::make_shared<raw_form_tree>(elem::NONE, rt948);
				sprawformtree ft944 = std::make_shared<raw_form_tree>(elem::AND, ft945, ft947);
				raw_rule rr949;
				rr949.h.push_back(rt943);
				rr949.set_prft(ft944);
				raw_term rt950;
				rt950.neg = true;
				rt950.extype = raw_term::REL;
				rt950.e.push_back(e874);
				rt950.e.push_back(e1);
				rt950.e.push_back(e804);
				rt950.e.push_back(e269);
				rt950.e.push_back(e239);
				rt950.e.push_back(e254);
				rt950.e.push_back(e208);
				rt950.e.push_back(e3);
				rt950.calc_arity(nullptr);
				raw_term rt951;
				rt951.neg = true;
				rt951.extype = raw_term::REL;
				rt951.e.push_back(e926);
				rt951.e.push_back(e1);
				rt951.e.push_back(e804);
				rt951.e.push_back(e269);
				rt951.e.push_back(e208);
				rt951.e.push_back(e3);
				rt951.calc_arity(nullptr);
				raw_term rt953;
				rt953.neg = false;
				rt953.extype = raw_term::REL;
				rt953.e.push_back(e887);
				rt953.e.push_back(e1);
				rt953.e.push_back(e804);
				rt953.e.push_back(e269);
				rt953.e.push_back(e165);
				rt953.e.push_back(e3);
				rt953.calc_arity(nullptr);
				sprawformtree ft952 = std::make_shared<raw_form_tree>(elem::NONE, rt953);
				raw_rule rr954;
				rr954.h.push_back(rt950);
				rr954.h.push_back(rt951);
				rr954.set_prft(ft952);
				raw_term rt955;
				rt955.neg = false;
				rt955.extype = raw_term::REL;
				rt955.e.push_back(e49);
				rt955.e.push_back(e1);
				rt955.e.push_back(e2);
				rt955.e.push_back(e3);
				rt955.calc_arity(nullptr);
				elem e961;
				e961.type = elem::VAR;
				e961.e = d.get_lexeme("?e0");
				elem e962;
				e962.type = elem::VAR;
				e962.e = d.get_lexeme("?e1");
				raw_term rt963;
				rt963.neg = false;
				rt963.extype = raw_term::REL;
				rt963.e.push_back(e6);
				rt963.e.push_back(e1);
				rt963.e.push_back(e40);
				rt963.e.push_back(e2);
				rt963.e.push_back(e961);
				rt963.e.push_back(e962);
				rt963.e.push_back(e3);
				rt963.calc_arity(nullptr);
				sprawformtree ft960 = std::make_shared<raw_form_tree>(elem::NONE, rt963);
				elem e965;
				e965.type = elem::VAR;
				e965.e = d.get_lexeme("?fs");
				raw_term rt966;
				rt966.neg = false;
				rt966.extype = raw_term::REL;
				rt966.e.push_back(e6);
				rt966.e.push_back(e1);
				rt966.e.push_back(e7);
				rt966.e.push_back(e961);
				rt966.e.push_back(e8);
				rt966.e.push_back(e208);
				rt966.e.push_back(e965);
				rt966.e.push_back(e3);
				rt966.calc_arity(nullptr);
				sprawformtree ft964 = std::make_shared<raw_form_tree>(elem::NONE, rt966);
				sprawformtree ft959 = std::make_shared<raw_form_tree>(elem::AND, ft960, ft964);
				sprawformtree ft969 = std::make_shared<raw_form_tree>(elem::VAR, e239);
				sprawformtree ft971 = std::make_shared<raw_form_tree>(elem::VAR, e254);
				elem e973;
				e973.type = elem::SYM;
				e973.e = d.get_lexeme("FORMULA_OUT");
				raw_term rt974;
				rt974.neg = false;
				rt974.extype = raw_term::REL;
				rt974.e.push_back(e973);
				rt974.e.push_back(e1);
				rt974.e.push_back(e962);
				rt974.e.push_back(e239);
				rt974.e.push_back(e254);
				rt974.e.push_back(e3);
				rt974.calc_arity(nullptr);
				sprawformtree ft972 = std::make_shared<raw_form_tree>(elem::NONE, rt974);
				sprawformtree ft970 = std::make_shared<raw_form_tree>(elem::EXISTS, ft971, ft972);
				sprawformtree ft968 = std::make_shared<raw_form_tree>(elem::EXISTS, ft969, ft970);
				sprawformtree ft967 = std::make_shared<raw_form_tree>(elem::NOT, ft968);
				sprawformtree ft958 = std::make_shared<raw_form_tree>(elem::AND, ft959, ft967);
				raw_term rt976;
				rt976.neg = false;
				rt976.extype = raw_term::REL;
				rt976.e.push_back(e45);
				rt976.e.push_back(e1);
				rt976.e.push_back(e3);
				rt976.calc_arity(nullptr);
				sprawformtree ft975 = std::make_shared<raw_form_tree>(elem::NONE, rt976);
				sprawformtree ft957 = std::make_shared<raw_form_tree>(elem::AND, ft958, ft975);
				raw_term rt979;
				rt979.neg = false;
				rt979.extype = raw_term::REL;
				rt979.e.push_back(e73);
				rt979.e.push_back(e1);
				rt979.e.push_back(e3);
				rt979.calc_arity(nullptr);
				sprawformtree ft978 = std::make_shared<raw_form_tree>(elem::NONE, rt979);
				sprawformtree ft977 = std::make_shared<raw_form_tree>(elem::NOT, ft978);
				sprawformtree ft956 = std::make_shared<raw_form_tree>(elem::AND, ft957, ft977);
				raw_rule rr980;
				rr980.h.push_back(rt955);
				rr980.set_prft(ft956);
				raw_term rt981;
				rt981.neg = false;
				rt981.extype = raw_term::REL;
				rt981.e.push_back(e471);
				rt981.e.push_back(e1);
				rt981.e.push_back(e239);
				rt981.e.push_back(e254);
				rt981.e.push_back(e208);
				rt981.e.push_back(e3);
				rt981.calc_arity(nullptr);
				raw_term rt982;
				rt982.neg = false;
				rt982.extype = raw_term::REL;
				rt982.e.push_back(e667);
				rt982.e.push_back(e1);
				rt982.e.push_back(e239);
				rt982.e.push_back(e254);
				rt982.e.push_back(e3);
				rt982.calc_arity(nullptr);
				raw_term rt983;
				rt983.neg = false;
				rt983.extype = raw_term::REL;
				rt983.e.push_back(e879);
				rt983.e.push_back(e1);
				rt983.e.push_back(e208);
				rt983.e.push_back(e965);
				rt983.e.push_back(e3);
				rt983.calc_arity(nullptr);
				raw_term rt989;
				rt989.neg = false;
				rt989.extype = raw_term::REL;
				rt989.e.push_back(e6);
				rt989.e.push_back(e1);
				rt989.e.push_back(e40);
				rt989.e.push_back(e2);
				rt989.e.push_back(e961);
				rt989.e.push_back(e962);
				rt989.e.push_back(e3);
				rt989.calc_arity(nullptr);
				sprawformtree ft988 = std::make_shared<raw_form_tree>(elem::NONE, rt989);
				raw_term rt991;
				rt991.neg = false;
				rt991.extype = raw_term::REL;
				rt991.e.push_back(e6);
				rt991.e.push_back(e1);
				rt991.e.push_back(e7);
				rt991.e.push_back(e961);
				rt991.e.push_back(e8);
				rt991.e.push_back(e208);
				rt991.e.push_back(e965);
				rt991.e.push_back(e3);
				rt991.calc_arity(nullptr);
				sprawformtree ft990 = std::make_shared<raw_form_tree>(elem::NONE, rt991);
				sprawformtree ft987 = std::make_shared<raw_form_tree>(elem::AND, ft988, ft990);
				raw_term rt993;
				rt993.neg = false;
				rt993.extype = raw_term::REL;
				rt993.e.push_back(e973);
				rt993.e.push_back(e1);
				rt993.e.push_back(e962);
				rt993.e.push_back(e239);
				rt993.e.push_back(e254);
				rt993.e.push_back(e3);
				rt993.calc_arity(nullptr);
				sprawformtree ft992 = std::make_shared<raw_form_tree>(elem::NONE, rt993);
				sprawformtree ft986 = std::make_shared<raw_form_tree>(elem::AND, ft987, ft992);
				raw_term rt995;
				rt995.neg = false;
				rt995.extype = raw_term::REL;
				rt995.e.push_back(e45);
				rt995.e.push_back(e1);
				rt995.e.push_back(e3);
				rt995.calc_arity(nullptr);
				sprawformtree ft994 = std::make_shared<raw_form_tree>(elem::NONE, rt995);
				sprawformtree ft985 = std::make_shared<raw_form_tree>(elem::AND, ft986, ft994);
				raw_term rt998;
				rt998.neg = false;
				rt998.extype = raw_term::REL;
				rt998.e.push_back(e73);
				rt998.e.push_back(e1);
				rt998.e.push_back(e3);
				rt998.calc_arity(nullptr);
				sprawformtree ft997 = std::make_shared<raw_form_tree>(elem::NONE, rt998);
				sprawformtree ft996 = std::make_shared<raw_form_tree>(elem::NOT, ft997);
				sprawformtree ft984 = std::make_shared<raw_form_tree>(elem::AND, ft985, ft996);
				raw_rule rr999;
				rr999.h.push_back(rt981);
				rr999.h.push_back(rt982);
				rr999.h.push_back(rt983);
				rr999.set_prft(ft984);
				elem e1000;
				e1000.type = elem::VAR;
				e1000.e = d.get_lexeme("?ds1");
				raw_term rt1001;
				rt1001.neg = false;
				rt1001.extype = raw_term::REL;
				rt1001.e.push_back(e879);
				rt1001.e.push_back(e1);
				rt1001.e.push_back(e1000);
				rt1001.e.push_back(e965);
				rt1001.e.push_back(e3);
				rt1001.calc_arity(nullptr);
				raw_term rt1007;
				rt1007.neg = false;
				rt1007.extype = raw_term::REL;
				rt1007.e.push_back(e6);
				rt1007.e.push_back(e1);
				rt1007.e.push_back(e40);
				rt1007.e.push_back(e2);
				rt1007.e.push_back(e961);
				rt1007.e.push_back(e962);
				rt1007.e.push_back(e3);
				rt1007.calc_arity(nullptr);
				sprawformtree ft1006 = std::make_shared<raw_form_tree>(elem::NONE, rt1007);
				raw_term rt1009;
				rt1009.neg = false;
				rt1009.extype = raw_term::REL;
				rt1009.e.push_back(e6);
				rt1009.e.push_back(e1);
				rt1009.e.push_back(e7);
				rt1009.e.push_back(e961);
				rt1009.e.push_back(e8);
				rt1009.e.push_back(e208);
				rt1009.e.push_back(e965);
				rt1009.e.push_back(e3);
				rt1009.calc_arity(nullptr);
				sprawformtree ft1008 = std::make_shared<raw_form_tree>(elem::NONE, rt1009);
				sprawformtree ft1005 = std::make_shared<raw_form_tree>(elem::AND, ft1006, ft1008);
				raw_term rt1011;
				rt1011.neg = false;
				rt1011.extype = raw_term::REL;
				rt1011.e.push_back(e973);
				rt1011.e.push_back(e1);
				rt1011.e.push_back(e962);
				rt1011.e.push_back(e239);
				rt1011.e.push_back(e254);
				rt1011.e.push_back(e3);
				rt1011.calc_arity(nullptr);
				sprawformtree ft1010 = std::make_shared<raw_form_tree>(elem::NONE, rt1011);
				sprawformtree ft1004 = std::make_shared<raw_form_tree>(elem::AND, ft1005, ft1010);
				raw_term rt1013;
				rt1013.neg = false;
				rt1013.extype = raw_term::REL;
				rt1013.e.push_back(e471);
				rt1013.e.push_back(e1);
				rt1013.e.push_back(e239);
				rt1013.e.push_back(e254);
				rt1013.e.push_back(e208);
				rt1013.e.push_back(e1000);
				rt1013.e.push_back(e3);
				rt1013.calc_arity(nullptr);
				sprawformtree ft1012 = std::make_shared<raw_form_tree>(elem::NONE, rt1013);
				sprawformtree ft1003 = std::make_shared<raw_form_tree>(elem::AND, ft1004, ft1012);
				raw_term rt1015;
				rt1015.neg = false;
				rt1015.extype = raw_term::REL;
				rt1015.e.push_back(e45);
				rt1015.e.push_back(e1);
				rt1015.e.push_back(e3);
				rt1015.calc_arity(nullptr);
				sprawformtree ft1014 = std::make_shared<raw_form_tree>(elem::NONE, rt1015);
				sprawformtree ft1002 = std::make_shared<raw_form_tree>(elem::AND, ft1003, ft1014);
				raw_rule rr1016;
				rr1016.h.push_back(rt1001);
				rr1016.set_prft(ft1002);
				raw_term rt1017;
				rt1017.neg = false;
				rt1017.extype = raw_term::REL;
				rt1017.e.push_back(e49);
				rt1017.e.push_back(e1);
				rt1017.e.push_back(e2);
				rt1017.e.push_back(e3);
				rt1017.calc_arity(nullptr);
				raw_term rt1026;
				rt1026.neg = false;
				rt1026.extype = raw_term::REL;
				rt1026.e.push_back(e6);
				rt1026.e.push_back(e1);
				rt1026.e.push_back(e40);
				rt1026.e.push_back(e2);
				rt1026.e.push_back(e961);
				rt1026.e.push_back(e962);
				rt1026.e.push_back(e3);
				rt1026.calc_arity(nullptr);
				sprawformtree ft1025 = std::make_shared<raw_form_tree>(elem::NONE, rt1026);
				raw_term rt1028;
				rt1028.neg = false;
				rt1028.extype = raw_term::REL;
				rt1028.e.push_back(e6);
				rt1028.e.push_back(e1);
				rt1028.e.push_back(e7);
				rt1028.e.push_back(e961);
				rt1028.e.push_back(e8);
				rt1028.e.push_back(e208);
				rt1028.e.push_back(e965);
				rt1028.e.push_back(e3);
				rt1028.calc_arity(nullptr);
				sprawformtree ft1027 = std::make_shared<raw_form_tree>(elem::NONE, rt1028);
				sprawformtree ft1024 = std::make_shared<raw_form_tree>(elem::AND, ft1025, ft1027);
				raw_term rt1030;
				rt1030.neg = false;
				rt1030.extype = raw_term::REL;
				rt1030.e.push_back(e973);
				rt1030.e.push_back(e1);
				rt1030.e.push_back(e962);
				rt1030.e.push_back(e239);
				rt1030.e.push_back(e254);
				rt1030.e.push_back(e3);
				rt1030.calc_arity(nullptr);
				sprawformtree ft1029 = std::make_shared<raw_form_tree>(elem::NONE, rt1030);
				sprawformtree ft1023 = std::make_shared<raw_form_tree>(elem::AND, ft1024, ft1029);
				raw_term rt1032;
				rt1032.neg = false;
				rt1032.extype = raw_term::REL;
				rt1032.e.push_back(e471);
				rt1032.e.push_back(e1);
				rt1032.e.push_back(e239);
				rt1032.e.push_back(e254);
				rt1032.e.push_back(e208);
				rt1032.e.push_back(e1000);
				rt1032.e.push_back(e3);
				rt1032.calc_arity(nullptr);
				sprawformtree ft1031 = std::make_shared<raw_form_tree>(elem::NONE, rt1032);
				sprawformtree ft1022 = std::make_shared<raw_form_tree>(elem::AND, ft1023, ft1031);
				elem e1034;
				e1034.type = elem::VAR;
				e1034.e = d.get_lexeme("?ds2");
				raw_term rt1035;
				rt1035.neg = false;
				rt1035.extype = raw_term::REL;
				rt1035.e.push_back(e887);
				rt1035.e.push_back(e1);
				rt1035.e.push_back(e1000);
				rt1035.e.push_back(e965);
				rt1035.e.push_back(e1034);
				rt1035.e.push_back(e3);
				rt1035.calc_arity(nullptr);
				sprawformtree ft1033 = std::make_shared<raw_form_tree>(elem::NONE, rt1035);
				sprawformtree ft1021 = std::make_shared<raw_form_tree>(elem::AND, ft1022, ft1033);
				elem e1037;
				e1037.type = elem::VAR;
				e1037.e = d.get_lexeme("?ds3");
				raw_term rt1038;
				rt1038.neg = false;
				rt1038.extype = raw_term::REL;
				rt1038.e.push_back(e887);
				rt1038.e.push_back(e1);
				rt1038.e.push_back(e208);
				rt1038.e.push_back(e965);
				rt1038.e.push_back(e1037);
				rt1038.e.push_back(e3);
				rt1038.calc_arity(nullptr);
				sprawformtree ft1036 = std::make_shared<raw_form_tree>(elem::NONE, rt1038);
				sprawformtree ft1020 = std::make_shared<raw_form_tree>(elem::AND, ft1021, ft1036);
				raw_term rt1041;
				rt1041.neg = false;
				rt1041.extype = raw_term::REL;
				rt1041.e.push_back(e671);
				rt1041.e.push_back(e1);
				rt1041.e.push_back(e239);
				rt1041.e.push_back(e254);
				rt1041.e.push_back(e3);
				rt1041.calc_arity(nullptr);
				sprawformtree ft1040 = std::make_shared<raw_form_tree>(elem::NONE, rt1041);
				raw_term rt1043;
				rt1043.neg = false;
				rt1043.extype = raw_term::REL;
				rt1043.e.push_back(e679);
				rt1043.e.push_back(e1);
				rt1043.e.push_back(e239);
				rt1043.e.push_back(e254);
				rt1043.e.push_back(e3);
				rt1043.calc_arity(nullptr);
				sprawformtree ft1042 = std::make_shared<raw_form_tree>(elem::NONE, rt1043);
				sprawformtree ft1039 = std::make_shared<raw_form_tree>(elem::ALT, ft1040, ft1042);
				sprawformtree ft1019 = std::make_shared<raw_form_tree>(elem::AND, ft1020, ft1039);
				raw_term rt1045;
				rt1045.neg = false;
				rt1045.extype = raw_term::REL;
				rt1045.e.push_back(e45);
				rt1045.e.push_back(e1);
				rt1045.e.push_back(e3);
				rt1045.calc_arity(nullptr);
				sprawformtree ft1044 = std::make_shared<raw_form_tree>(elem::NONE, rt1045);
				sprawformtree ft1018 = std::make_shared<raw_form_tree>(elem::AND, ft1019, ft1044);
				raw_rule rr1046;
				rr1046.h.push_back(rt1017);
				rr1046.set_prft(ft1018);
				elem &e1047 = out_rel;
				raw_term rt1048;
				rt1048.neg = false;
				rt1048.extype = raw_term::REL;
				rt1048.e.push_back(e1047);
				rt1048.e.push_back(e1);
				rt1048.e.push_back(e8);
				rt1048.e.push_back(e861);
				rt1048.e.push_back(e3);
				rt1048.calc_arity(nullptr);
				raw_term rt1057;
				rt1057.neg = false;
				rt1057.extype = raw_term::REL;
				rt1057.e.push_back(e6);
				rt1057.e.push_back(e1);
				rt1057.e.push_back(e40);
				rt1057.e.push_back(e2);
				rt1057.e.push_back(e961);
				rt1057.e.push_back(e962);
				rt1057.e.push_back(e3);
				rt1057.calc_arity(nullptr);
				sprawformtree ft1056 = std::make_shared<raw_form_tree>(elem::NONE, rt1057);
				raw_term rt1059;
				rt1059.neg = false;
				rt1059.extype = raw_term::REL;
				rt1059.e.push_back(e6);
				rt1059.e.push_back(e1);
				rt1059.e.push_back(e7);
				rt1059.e.push_back(e961);
				rt1059.e.push_back(e8);
				rt1059.e.push_back(e208);
				rt1059.e.push_back(e965);
				rt1059.e.push_back(e3);
				rt1059.calc_arity(nullptr);
				sprawformtree ft1058 = std::make_shared<raw_form_tree>(elem::NONE, rt1059);
				sprawformtree ft1055 = std::make_shared<raw_form_tree>(elem::AND, ft1056, ft1058);
				raw_term rt1061;
				rt1061.neg = false;
				rt1061.extype = raw_term::REL;
				rt1061.e.push_back(e973);
				rt1061.e.push_back(e1);
				rt1061.e.push_back(e962);
				rt1061.e.push_back(e239);
				rt1061.e.push_back(e254);
				rt1061.e.push_back(e3);
				rt1061.calc_arity(nullptr);
				sprawformtree ft1060 = std::make_shared<raw_form_tree>(elem::NONE, rt1061);
				sprawformtree ft1054 = std::make_shared<raw_form_tree>(elem::AND, ft1055, ft1060);
				elem e1063;
				e1063.type = elem::VAR;
				e1063.e = d.get_lexeme("?gs");
				raw_term rt1064;
				rt1064.neg = false;
				rt1064.extype = raw_term::REL;
				rt1064.e.push_back(e887);
				rt1064.e.push_back(e1);
				rt1064.e.push_back(e208);
				rt1064.e.push_back(e965);
				rt1064.e.push_back(e1063);
				rt1064.e.push_back(e3);
				rt1064.calc_arity(nullptr);
				sprawformtree ft1062 = std::make_shared<raw_form_tree>(elem::NONE, rt1064);
				sprawformtree ft1053 = std::make_shared<raw_form_tree>(elem::AND, ft1054, ft1062);
				raw_term rt1066;
				rt1066.neg = false;
				rt1066.extype = raw_term::REL;
				rt1066.e.push_back(e887);
				rt1066.e.push_back(e1);
				rt1066.e.push_back(e861);
				rt1066.e.push_back(e965);
				rt1066.e.push_back(e1063);
				rt1066.e.push_back(e3);
				rt1066.calc_arity(nullptr);
				sprawformtree ft1065 = std::make_shared<raw_form_tree>(elem::NONE, rt1066);
				sprawformtree ft1052 = std::make_shared<raw_form_tree>(elem::AND, ft1053, ft1065);
				raw_term rt1068;
				rt1068.neg = false;
				rt1068.extype = raw_term::REL;
				rt1068.e.push_back(e471);
				rt1068.e.push_back(e1);
				rt1068.e.push_back(e239);
				rt1068.e.push_back(e254);
				rt1068.e.push_back(e208);
				rt1068.e.push_back(e861);
				rt1068.e.push_back(e3);
				rt1068.calc_arity(nullptr);
				sprawformtree ft1067 = std::make_shared<raw_form_tree>(elem::NONE, rt1068);
				sprawformtree ft1051 = std::make_shared<raw_form_tree>(elem::AND, ft1052, ft1067);
				raw_term rt1070;
				rt1070.neg = false;
				rt1070.extype = raw_term::REL;
				rt1070.e.push_back(e671);
				rt1070.e.push_back(e1);
				rt1070.e.push_back(e239);
				rt1070.e.push_back(e254);
				rt1070.e.push_back(e3);
				rt1070.calc_arity(nullptr);
				sprawformtree ft1069 = std::make_shared<raw_form_tree>(elem::NONE, rt1070);
				sprawformtree ft1050 = std::make_shared<raw_form_tree>(elem::AND, ft1051, ft1069);
				raw_term rt1072;
				rt1072.neg = false;
				rt1072.extype = raw_term::REL;
				rt1072.e.push_back(e45);
				rt1072.e.push_back(e1);
				rt1072.e.push_back(e3);
				rt1072.calc_arity(nullptr);
				sprawformtree ft1071 = std::make_shared<raw_form_tree>(elem::NONE, rt1072);
				sprawformtree ft1049 = std::make_shared<raw_form_tree>(elem::AND, ft1050, ft1071);
				raw_rule rr1073;
				rr1073.h.push_back(rt1048);
				rr1073.set_prft(ft1049);
				raw_term rt1074;
				rt1074.neg = false;
				rt1074.extype = raw_term::REL;
				rt1074.e.push_back(e879);
				rt1074.e.push_back(e1);
				rt1074.e.push_back(e239);
				rt1074.e.push_back(e254);
				rt1074.e.push_back(e3);
				rt1074.calc_arity(nullptr);
				raw_term rt1075;
				rt1075.neg = false;
				rt1075.extype = raw_term::REL;
				rt1075.e.push_back(e793);
				rt1075.e.push_back(e1);
				rt1075.e.push_back(e239);
				rt1075.e.push_back(e254);
				rt1075.e.push_back(e3);
				rt1075.calc_arity(nullptr);
				elem e1079;
				e1079.type = elem::VAR;
				e1079.e = d.get_lexeme("?n");
				raw_term rt1080;
				rt1080.neg = false;
				rt1080.extype = raw_term::REL;
				rt1080.e.push_back(e6);
				rt1080.e.push_back(e1);
				rt1080.e.push_back(e7);
				rt1080.e.push_back(e2);
				rt1080.e.push_back(e1079);
				rt1080.e.push_back(e239);
				rt1080.e.push_back(e254);
				rt1080.e.push_back(e3);
				rt1080.calc_arity(nullptr);
				sprawformtree ft1078 = std::make_shared<raw_form_tree>(elem::NONE, rt1080);
				raw_term rt1082;
				rt1082.neg = false;
				rt1082.extype = raw_term::REL;
				rt1082.e.push_back(e47);
				rt1082.e.push_back(e1);
				rt1082.e.push_back(e3);
				rt1082.calc_arity(nullptr);
				sprawformtree ft1081 = std::make_shared<raw_form_tree>(elem::NONE, rt1082);
				sprawformtree ft1077 = std::make_shared<raw_form_tree>(elem::AND, ft1078, ft1081);
				raw_term rt1085;
				rt1085.neg = false;
				rt1085.extype = raw_term::REL;
				rt1085.e.push_back(e55);
				rt1085.e.push_back(e1);
				rt1085.e.push_back(e3);
				rt1085.calc_arity(nullptr);
				sprawformtree ft1084 = std::make_shared<raw_form_tree>(elem::NONE, rt1085);
				sprawformtree ft1083 = std::make_shared<raw_form_tree>(elem::NOT, ft1084);
				sprawformtree ft1076 = std::make_shared<raw_form_tree>(elem::AND, ft1077, ft1083);
				raw_rule rr1086;
				rr1086.h.push_back(rt1074);
				rr1086.h.push_back(rt1075);
				rr1086.set_prft(ft1076);
				raw_term rt1087;
				rt1087.neg = false;
				rt1087.extype = raw_term::REL;
				rt1087.e.push_back(e70);
				rt1087.e.push_back(e1);
				rt1087.e.push_back(e2);
				rt1087.e.push_back(e239);
				rt1087.e.push_back(e3);
				rt1087.calc_arity(nullptr);
				raw_term rt1092;
				rt1092.neg = false;
				rt1092.extype = raw_term::REL;
				rt1092.e.push_back(e6);
				rt1092.e.push_back(e1);
				rt1092.e.push_back(e7);
				rt1092.e.push_back(e2);
				rt1092.e.push_back(e1079);
				rt1092.e.push_back(e239);
				rt1092.e.push_back(e254);
				rt1092.e.push_back(e3);
				rt1092.calc_arity(nullptr);
				sprawformtree ft1091 = std::make_shared<raw_form_tree>(elem::NONE, rt1092);
				raw_term rt1094;
				rt1094.neg = false;
				rt1094.extype = raw_term::REL;
				rt1094.e.push_back(e887);
				rt1094.e.push_back(e1);
				rt1094.e.push_back(e239);
				rt1094.e.push_back(e254);
				rt1094.e.push_back(e208);
				rt1094.e.push_back(e3);
				rt1094.calc_arity(nullptr);
				sprawformtree ft1093 = std::make_shared<raw_form_tree>(elem::NONE, rt1094);
				sprawformtree ft1090 = std::make_shared<raw_form_tree>(elem::AND, ft1091, ft1093);
				raw_term rt1096;
				rt1096.neg = false;
				rt1096.extype = raw_term::REL;
				rt1096.e.push_back(e801);
				rt1096.e.push_back(e1);
				rt1096.e.push_back(e239);
				rt1096.e.push_back(e254);
				rt1096.e.push_back(e861);
				rt1096.e.push_back(e3);
				rt1096.calc_arity(nullptr);
				sprawformtree ft1095 = std::make_shared<raw_form_tree>(elem::NONE, rt1096);
				sprawformtree ft1089 = std::make_shared<raw_form_tree>(elem::AND, ft1090, ft1095);
				raw_term rt1098;
				rt1098.neg = false;
				rt1098.extype = raw_term::REL;
				rt1098.e.push_back(e47);
				rt1098.e.push_back(e1);
				rt1098.e.push_back(e3);
				rt1098.calc_arity(nullptr);
				sprawformtree ft1097 = std::make_shared<raw_form_tree>(elem::NONE, rt1098);
				sprawformtree ft1088 = std::make_shared<raw_form_tree>(elem::AND, ft1089, ft1097);
				raw_rule rr1099;
				rr1099.h.push_back(rt1087);
				rr1099.set_prft(ft1088);
				raw_term rt1100;
				rt1100.neg = false;
				rt1100.extype = raw_term::REL;
				rt1100.e.push_back(e879);
				rt1100.e.push_back(e1);
				rt1100.e.push_back(e208);
				rt1100.e.push_back(e254);
				rt1100.e.push_back(e3);
				rt1100.calc_arity(nullptr);
				raw_term rt1101;
				rt1101.neg = false;
				rt1101.extype = raw_term::REL;
				rt1101.e.push_back(e793);
				rt1101.e.push_back(e1);
				rt1101.e.push_back(e208);
				rt1101.e.push_back(e254);
				rt1101.e.push_back(e3);
				rt1101.calc_arity(nullptr);
				raw_term rt1106;
				rt1106.neg = false;
				rt1106.extype = raw_term::REL;
				rt1106.e.push_back(e6);
				rt1106.e.push_back(e1);
				rt1106.e.push_back(e7);
				rt1106.e.push_back(e2);
				rt1106.e.push_back(e1079);
				rt1106.e.push_back(e239);
				rt1106.e.push_back(e254);
				rt1106.e.push_back(e3);
				rt1106.calc_arity(nullptr);
				sprawformtree ft1105 = std::make_shared<raw_form_tree>(elem::NONE, rt1106);
				raw_term rt1108;
				rt1108.neg = false;
				rt1108.extype = raw_term::REL;
				rt1108.e.push_back(e1047);
				rt1108.e.push_back(e1);
				rt1108.e.push_back(e1079);
				rt1108.e.push_back(e208);
				rt1108.e.push_back(e3);
				rt1108.calc_arity(nullptr);
				sprawformtree ft1107 = std::make_shared<raw_form_tree>(elem::NONE, rt1108);
				sprawformtree ft1104 = std::make_shared<raw_form_tree>(elem::AND, ft1105, ft1107);
				raw_term rt1110;
				rt1110.neg = false;
				rt1110.extype = raw_term::REL;
				rt1110.e.push_back(e47);
				rt1110.e.push_back(e1);
				rt1110.e.push_back(e3);
				rt1110.calc_arity(nullptr);
				sprawformtree ft1109 = std::make_shared<raw_form_tree>(elem::NONE, rt1110);
				sprawformtree ft1103 = std::make_shared<raw_form_tree>(elem::AND, ft1104, ft1109);
				raw_term rt1113;
				rt1113.neg = false;
				rt1113.extype = raw_term::REL;
				rt1113.e.push_back(e55);
				rt1113.e.push_back(e1);
				rt1113.e.push_back(e3);
				rt1113.calc_arity(nullptr);
				sprawformtree ft1112 = std::make_shared<raw_form_tree>(elem::NONE, rt1113);
				sprawformtree ft1111 = std::make_shared<raw_form_tree>(elem::NOT, ft1112);
				sprawformtree ft1102 = std::make_shared<raw_form_tree>(elem::AND, ft1103, ft1111);
				raw_rule rr1114;
				rr1114.h.push_back(rt1100);
				rr1114.h.push_back(rt1101);
				rr1114.set_prft(ft1102);
				elem e1115;
				e1115.type = elem::VAR;
				e1115.e = d.get_lexeme("?es");
				raw_term rt1116;
				rt1116.neg = false;
				rt1116.extype = raw_term::REL;
				rt1116.e.push_back(e973);
				rt1116.e.push_back(e1);
				rt1116.e.push_back(e2);
				rt1116.e.push_back(e1115);
				rt1116.e.push_back(e965);
				rt1116.e.push_back(e3);
				rt1116.calc_arity(nullptr);
				raw_term rt1124;
				rt1124.neg = false;
				rt1124.extype = raw_term::REL;
				rt1124.e.push_back(e6);
				rt1124.e.push_back(e1);
				rt1124.e.push_back(e7);
				rt1124.e.push_back(e2);
				rt1124.e.push_back(e1079);
				rt1124.e.push_back(e239);
				rt1124.e.push_back(e254);
				rt1124.e.push_back(e3);
				rt1124.calc_arity(nullptr);
				sprawformtree ft1123 = std::make_shared<raw_form_tree>(elem::NONE, rt1124);
				raw_term rt1126;
				rt1126.neg = false;
				rt1126.extype = raw_term::REL;
				rt1126.e.push_back(e1047);
				rt1126.e.push_back(e1);
				rt1126.e.push_back(e1079);
				rt1126.e.push_back(e208);
				rt1126.e.push_back(e3);
				rt1126.calc_arity(nullptr);
				sprawformtree ft1125 = std::make_shared<raw_form_tree>(elem::NONE, rt1126);
				sprawformtree ft1122 = std::make_shared<raw_form_tree>(elem::AND, ft1123, ft1125);
				raw_term rt1128;
				rt1128.neg = false;
				rt1128.extype = raw_term::REL;
				rt1128.e.push_back(e801);
				rt1128.e.push_back(e1);
				rt1128.e.push_back(e239);
				rt1128.e.push_back(e254);
				rt1128.e.push_back(e1115);
				rt1128.e.push_back(e3);
				rt1128.calc_arity(nullptr);
				sprawformtree ft1127 = std::make_shared<raw_form_tree>(elem::NONE, rt1128);
				sprawformtree ft1121 = std::make_shared<raw_form_tree>(elem::AND, ft1122, ft1127);
				raw_term rt1130;
				rt1130.neg = false;
				rt1130.extype = raw_term::REL;
				rt1130.e.push_back(e801);
				rt1130.e.push_back(e1);
				rt1130.e.push_back(e208);
				rt1130.e.push_back(e254);
				rt1130.e.push_back(e965);
				rt1130.e.push_back(e3);
				rt1130.calc_arity(nullptr);
				sprawformtree ft1129 = std::make_shared<raw_form_tree>(elem::NONE, rt1130);
				sprawformtree ft1120 = std::make_shared<raw_form_tree>(elem::AND, ft1121, ft1129);
				raw_term rt1132;
				rt1132.neg = false;
				rt1132.extype = raw_term::REL;
				rt1132.e.push_back(e887);
				rt1132.e.push_back(e1);
				rt1132.e.push_back(e208);
				rt1132.e.push_back(e254);
				rt1132.e.push_back(e861);
				rt1132.e.push_back(e3);
				rt1132.calc_arity(nullptr);
				sprawformtree ft1131 = std::make_shared<raw_form_tree>(elem::NONE, rt1132);
				sprawformtree ft1119 = std::make_shared<raw_form_tree>(elem::AND, ft1120, ft1131);
				raw_term rt1134;
				rt1134.neg = false;
				rt1134.extype = raw_term::REL;
				rt1134.e.push_back(e887);
				rt1134.e.push_back(e1);
				rt1134.e.push_back(e239);
				rt1134.e.push_back(e254);
				rt1134.e.push_back(e861);
				rt1134.e.push_back(e3);
				rt1134.calc_arity(nullptr);
				sprawformtree ft1133 = std::make_shared<raw_form_tree>(elem::NONE, rt1134);
				sprawformtree ft1118 = std::make_shared<raw_form_tree>(elem::AND, ft1119, ft1133);
				raw_term rt1136;
				rt1136.neg = false;
				rt1136.extype = raw_term::REL;
				rt1136.e.push_back(e47);
				rt1136.e.push_back(e1);
				rt1136.e.push_back(e3);
				rt1136.calc_arity(nullptr);
				sprawformtree ft1135 = std::make_shared<raw_form_tree>(elem::NONE, rt1136);
				sprawformtree ft1117 = std::make_shared<raw_form_tree>(elem::AND, ft1118, ft1135);
				raw_rule rr1137;
				rr1137.h.push_back(rt1116);
				rr1137.set_prft(ft1117);
				raw_term rt1138;
				rt1138.neg = false;
				rt1138.extype = raw_term::REL;
				rt1138.e.push_back(e973);
				rt1138.e.push_back(e1);
				rt1138.e.push_back(e2);
				rt1138.e.push_back(e239);
				rt1138.e.push_back(e254);
				rt1138.e.push_back(e3);
				rt1138.calc_arity(nullptr);
				elem e1144;
				e1144.type = elem::VAR;
				e1144.e = d.get_lexeme("?a1");
				elem e1145;
				e1145.type = elem::VAR;
				e1145.e = d.get_lexeme("?a2");
				raw_term rt1146;
				rt1146.neg = false;
				rt1146.extype = raw_term::REL;
				rt1146.e.push_back(e6);
				rt1146.e.push_back(e1);
				rt1146.e.push_back(e15);
				rt1146.e.push_back(e2);
				rt1146.e.push_back(e1144);
				rt1146.e.push_back(e1145);
				rt1146.e.push_back(e111);
				rt1146.e.push_back(e111);
				rt1146.e.push_back(e3);
				rt1146.calc_arity(nullptr);
				sprawformtree ft1143 = std::make_shared<raw_form_tree>(elem::NONE, rt1146);
				raw_term rt1148;
				rt1148.neg = false;
				rt1148.extype = raw_term::REL;
				rt1148.e.push_back(e160);
				rt1148.e.push_back(e1);
				rt1148.e.push_back(e239);
				rt1148.e.push_back(e3);
				rt1148.calc_arity(nullptr);
				sprawformtree ft1147 = std::make_shared<raw_form_tree>(elem::NONE, rt1148);
				sprawformtree ft1142 = std::make_shared<raw_form_tree>(elem::AND, ft1143, ft1147);
				raw_term rt1150;
				rt1150.neg = false;
				rt1150.extype = raw_term::REL;
				rt1150.e.push_back(e160);
				rt1150.e.push_back(e1);
				rt1150.e.push_back(e254);
				rt1150.e.push_back(e3);
				rt1150.calc_arity(nullptr);
				sprawformtree ft1149 = std::make_shared<raw_form_tree>(elem::NONE, rt1150);
				sprawformtree ft1141 = std::make_shared<raw_form_tree>(elem::AND, ft1142, ft1149);
				raw_term rt1152;
				rt1152.neg = false;
				rt1152.extype = raw_term::EQ;
				rt1152.e.push_back(e1144);
				rt1152.e.push_back(e112);
				rt1152.e.push_back(e1145);
				rt1152.calc_arity(nullptr);
				sprawformtree ft1151 = std::make_shared<raw_form_tree>(elem::NONE, rt1152);
				sprawformtree ft1140 = std::make_shared<raw_form_tree>(elem::AND, ft1141, ft1151);
				raw_term rt1154;
				rt1154.neg = false;
				rt1154.extype = raw_term::REL;
				rt1154.e.push_back(e47);
				rt1154.e.push_back(e1);
				rt1154.e.push_back(e3);
				rt1154.calc_arity(nullptr);
				sprawformtree ft1153 = std::make_shared<raw_form_tree>(elem::NONE, rt1154);
				sprawformtree ft1139 = std::make_shared<raw_form_tree>(elem::AND, ft1140, ft1153);
				raw_rule rr1155;
				rr1155.h.push_back(rt1138);
				rr1155.set_prft(ft1139);
				raw_term rt1156;
				rt1156.neg = false;
				rt1156.extype = raw_term::REL;
				rt1156.e.push_back(e70);
				rt1156.e.push_back(e1);
				rt1156.e.push_back(e2);
				rt1156.e.push_back(e239);
				rt1156.e.push_back(e3);
				rt1156.calc_arity(nullptr);
				raw_term rt1160;
				rt1160.neg = false;
				rt1160.extype = raw_term::REL;
				rt1160.e.push_back(e6);
				rt1160.e.push_back(e1);
				rt1160.e.push_back(e15);
				rt1160.e.push_back(e2);
				rt1160.e.push_back(e1144);
				rt1160.e.push_back(e1145);
				rt1160.e.push_back(e111);
				rt1160.e.push_back(e111);
				rt1160.e.push_back(e3);
				rt1160.calc_arity(nullptr);
				sprawformtree ft1159 = std::make_shared<raw_form_tree>(elem::NONE, rt1160);
				raw_term rt1162;
				rt1162.neg = false;
				rt1162.extype = raw_term::REL;
				rt1162.e.push_back(e160);
				rt1162.e.push_back(e1);
				rt1162.e.push_back(e239);
				rt1162.e.push_back(e3);
				rt1162.calc_arity(nullptr);
				sprawformtree ft1161 = std::make_shared<raw_form_tree>(elem::NONE, rt1162);
				sprawformtree ft1158 = std::make_shared<raw_form_tree>(elem::AND, ft1159, ft1161);
				raw_term rt1164;
				rt1164.neg = false;
				rt1164.extype = raw_term::REL;
				rt1164.e.push_back(e47);
				rt1164.e.push_back(e1);
				rt1164.e.push_back(e3);
				rt1164.calc_arity(nullptr);
				sprawformtree ft1163 = std::make_shared<raw_form_tree>(elem::NONE, rt1164);
				sprawformtree ft1157 = std::make_shared<raw_form_tree>(elem::AND, ft1158, ft1163);
				raw_rule rr1165;
				rr1165.h.push_back(rt1156);
				rr1165.set_prft(ft1157);
				raw_term rt1166;
				rt1166.neg = false;
				rt1166.extype = raw_term::REL;
				rt1166.e.push_back(e973);
				rt1166.e.push_back(e1);
				rt1166.e.push_back(e2);
				rt1166.e.push_back(e239);
				rt1166.e.push_back(e254);
				rt1166.e.push_back(e3);
				rt1166.calc_arity(nullptr);
				raw_term rt1171;
				rt1171.neg = false;
				rt1171.extype = raw_term::REL;
				rt1171.e.push_back(e6);
				rt1171.e.push_back(e1);
				rt1171.e.push_back(e15);
				rt1171.e.push_back(e2);
				rt1171.e.push_back(e1144);
				rt1171.e.push_back(e1145);
				rt1171.e.push_back(e111);
				rt1171.e.push_back(e817);
				rt1171.e.push_back(e3);
				rt1171.calc_arity(nullptr);
				sprawformtree ft1170 = std::make_shared<raw_form_tree>(elem::NONE, rt1171);
				raw_term rt1173;
				rt1173.neg = false;
				rt1173.extype = raw_term::REL;
				rt1173.e.push_back(e160);
				rt1173.e.push_back(e1);
				rt1173.e.push_back(e239);
				rt1173.e.push_back(e1145);
				rt1173.e.push_back(e3);
				rt1173.calc_arity(nullptr);
				sprawformtree ft1172 = std::make_shared<raw_form_tree>(elem::NONE, rt1173);
				sprawformtree ft1169 = std::make_shared<raw_form_tree>(elem::AND, ft1170, ft1172);
				raw_term rt1175;
				rt1175.neg = false;
				rt1175.extype = raw_term::REL;
				rt1175.e.push_back(e160);
				rt1175.e.push_back(e1);
				rt1175.e.push_back(e254);
				rt1175.e.push_back(e1144);
				rt1175.e.push_back(e3);
				rt1175.calc_arity(nullptr);
				sprawformtree ft1174 = std::make_shared<raw_form_tree>(elem::NONE, rt1175);
				sprawformtree ft1168 = std::make_shared<raw_form_tree>(elem::AND, ft1169, ft1174);
				raw_term rt1177;
				rt1177.neg = false;
				rt1177.extype = raw_term::REL;
				rt1177.e.push_back(e47);
				rt1177.e.push_back(e1);
				rt1177.e.push_back(e3);
				rt1177.calc_arity(nullptr);
				sprawformtree ft1176 = std::make_shared<raw_form_tree>(elem::NONE, rt1177);
				sprawformtree ft1167 = std::make_shared<raw_form_tree>(elem::AND, ft1168, ft1176);
				raw_rule rr1178;
				rr1178.h.push_back(rt1166);
				rr1178.set_prft(ft1167);
				raw_term rt1179;
				rt1179.neg = false;
				rt1179.extype = raw_term::REL;
				rt1179.e.push_back(e70);
				rt1179.e.push_back(e1);
				rt1179.e.push_back(e2);
				rt1179.e.push_back(e239);
				rt1179.e.push_back(e3);
				rt1179.calc_arity(nullptr);
				raw_term rt1183;
				rt1183.neg = false;
				rt1183.extype = raw_term::REL;
				rt1183.e.push_back(e6);
				rt1183.e.push_back(e1);
				rt1183.e.push_back(e15);
				rt1183.e.push_back(e2);
				rt1183.e.push_back(e1144);
				rt1183.e.push_back(e1145);
				rt1183.e.push_back(e111);
				rt1183.e.push_back(e817);
				rt1183.e.push_back(e3);
				rt1183.calc_arity(nullptr);
				sprawformtree ft1182 = std::make_shared<raw_form_tree>(elem::NONE, rt1183);
				raw_term rt1185;
				rt1185.neg = false;
				rt1185.extype = raw_term::REL;
				rt1185.e.push_back(e160);
				rt1185.e.push_back(e1);
				rt1185.e.push_back(e239);
				rt1185.e.push_back(e1145);
				rt1185.e.push_back(e3);
				rt1185.calc_arity(nullptr);
				sprawformtree ft1184 = std::make_shared<raw_form_tree>(elem::NONE, rt1185);
				sprawformtree ft1181 = std::make_shared<raw_form_tree>(elem::AND, ft1182, ft1184);
				raw_term rt1187;
				rt1187.neg = false;
				rt1187.extype = raw_term::REL;
				rt1187.e.push_back(e47);
				rt1187.e.push_back(e1);
				rt1187.e.push_back(e3);
				rt1187.calc_arity(nullptr);
				sprawformtree ft1186 = std::make_shared<raw_form_tree>(elem::NONE, rt1187);
				sprawformtree ft1180 = std::make_shared<raw_form_tree>(elem::AND, ft1181, ft1186);
				raw_rule rr1188;
				rr1188.h.push_back(rt1179);
				rr1188.set_prft(ft1180);
				raw_term rt1189;
				rt1189.neg = false;
				rt1189.extype = raw_term::REL;
				rt1189.e.push_back(e973);
				rt1189.e.push_back(e1);
				rt1189.e.push_back(e2);
				rt1189.e.push_back(e239);
				rt1189.e.push_back(e254);
				rt1189.e.push_back(e3);
				rt1189.calc_arity(nullptr);
				raw_term rt1194;
				rt1194.neg = false;
				rt1194.extype = raw_term::REL;
				rt1194.e.push_back(e6);
				rt1194.e.push_back(e1);
				rt1194.e.push_back(e15);
				rt1194.e.push_back(e2);
				rt1194.e.push_back(e1144);
				rt1194.e.push_back(e1145);
				rt1194.e.push_back(e817);
				rt1194.e.push_back(e111);
				rt1194.e.push_back(e3);
				rt1194.calc_arity(nullptr);
				sprawformtree ft1193 = std::make_shared<raw_form_tree>(elem::NONE, rt1194);
				raw_term rt1196;
				rt1196.neg = false;
				rt1196.extype = raw_term::REL;
				rt1196.e.push_back(e160);
				rt1196.e.push_back(e1);
				rt1196.e.push_back(e239);
				rt1196.e.push_back(e1144);
				rt1196.e.push_back(e3);
				rt1196.calc_arity(nullptr);
				sprawformtree ft1195 = std::make_shared<raw_form_tree>(elem::NONE, rt1196);
				sprawformtree ft1192 = std::make_shared<raw_form_tree>(elem::AND, ft1193, ft1195);
				raw_term rt1198;
				rt1198.neg = false;
				rt1198.extype = raw_term::REL;
				rt1198.e.push_back(e160);
				rt1198.e.push_back(e1);
				rt1198.e.push_back(e254);
				rt1198.e.push_back(e1145);
				rt1198.e.push_back(e3);
				rt1198.calc_arity(nullptr);
				sprawformtree ft1197 = std::make_shared<raw_form_tree>(elem::NONE, rt1198);
				sprawformtree ft1191 = std::make_shared<raw_form_tree>(elem::AND, ft1192, ft1197);
				raw_term rt1200;
				rt1200.neg = false;
				rt1200.extype = raw_term::REL;
				rt1200.e.push_back(e47);
				rt1200.e.push_back(e1);
				rt1200.e.push_back(e3);
				rt1200.calc_arity(nullptr);
				sprawformtree ft1199 = std::make_shared<raw_form_tree>(elem::NONE, rt1200);
				sprawformtree ft1190 = std::make_shared<raw_form_tree>(elem::AND, ft1191, ft1199);
				raw_rule rr1201;
				rr1201.h.push_back(rt1189);
				rr1201.set_prft(ft1190);
				raw_term rt1202;
				rt1202.neg = false;
				rt1202.extype = raw_term::REL;
				rt1202.e.push_back(e70);
				rt1202.e.push_back(e1);
				rt1202.e.push_back(e2);
				rt1202.e.push_back(e239);
				rt1202.e.push_back(e3);
				rt1202.calc_arity(nullptr);
				raw_term rt1206;
				rt1206.neg = false;
				rt1206.extype = raw_term::REL;
				rt1206.e.push_back(e6);
				rt1206.e.push_back(e1);
				rt1206.e.push_back(e15);
				rt1206.e.push_back(e2);
				rt1206.e.push_back(e1144);
				rt1206.e.push_back(e1145);
				rt1206.e.push_back(e817);
				rt1206.e.push_back(e111);
				rt1206.e.push_back(e3);
				rt1206.calc_arity(nullptr);
				sprawformtree ft1205 = std::make_shared<raw_form_tree>(elem::NONE, rt1206);
				raw_term rt1208;
				rt1208.neg = false;
				rt1208.extype = raw_term::REL;
				rt1208.e.push_back(e160);
				rt1208.e.push_back(e1);
				rt1208.e.push_back(e239);
				rt1208.e.push_back(e1144);
				rt1208.e.push_back(e3);
				rt1208.calc_arity(nullptr);
				sprawformtree ft1207 = std::make_shared<raw_form_tree>(elem::NONE, rt1208);
				sprawformtree ft1204 = std::make_shared<raw_form_tree>(elem::AND, ft1205, ft1207);
				raw_term rt1210;
				rt1210.neg = false;
				rt1210.extype = raw_term::REL;
				rt1210.e.push_back(e47);
				rt1210.e.push_back(e1);
				rt1210.e.push_back(e3);
				rt1210.calc_arity(nullptr);
				sprawformtree ft1209 = std::make_shared<raw_form_tree>(elem::NONE, rt1210);
				sprawformtree ft1203 = std::make_shared<raw_form_tree>(elem::AND, ft1204, ft1209);
				raw_rule rr1211;
				rr1211.h.push_back(rt1202);
				rr1211.set_prft(ft1203);
				raw_term rt1212;
				rt1212.neg = false;
				rt1212.extype = raw_term::REL;
				rt1212.e.push_back(e973);
				rt1212.e.push_back(e1);
				rt1212.e.push_back(e2);
				rt1212.e.push_back(e239);
				rt1212.e.push_back(e254);
				rt1212.e.push_back(e3);
				rt1212.calc_arity(nullptr);
				raw_term rt1218;
				rt1218.neg = false;
				rt1218.extype = raw_term::REL;
				rt1218.e.push_back(e6);
				rt1218.e.push_back(e1);
				rt1218.e.push_back(e15);
				rt1218.e.push_back(e2);
				rt1218.e.push_back(e1144);
				rt1218.e.push_back(e1145);
				rt1218.e.push_back(e817);
				rt1218.e.push_back(e817);
				rt1218.e.push_back(e3);
				rt1218.calc_arity(nullptr);
				sprawformtree ft1217 = std::make_shared<raw_form_tree>(elem::NONE, rt1218);
				raw_term rt1220;
				rt1220.neg = false;
				rt1220.extype = raw_term::REL;
				rt1220.e.push_back(e160);
				rt1220.e.push_back(e1);
				rt1220.e.push_back(e239);
				rt1220.e.push_back(e1144);
				rt1220.e.push_back(e1145);
				rt1220.e.push_back(e3);
				rt1220.calc_arity(nullptr);
				sprawformtree ft1219 = std::make_shared<raw_form_tree>(elem::NONE, rt1220);
				sprawformtree ft1216 = std::make_shared<raw_form_tree>(elem::AND, ft1217, ft1219);
				raw_term rt1222;
				rt1222.neg = false;
				rt1222.extype = raw_term::REL;
				rt1222.e.push_back(e160);
				rt1222.e.push_back(e1);
				rt1222.e.push_back(e254);
				rt1222.e.push_back(e23);
				rt1222.e.push_back(e24);
				rt1222.e.push_back(e3);
				rt1222.calc_arity(nullptr);
				sprawformtree ft1221 = std::make_shared<raw_form_tree>(elem::NONE, rt1222);
				sprawformtree ft1215 = std::make_shared<raw_form_tree>(elem::AND, ft1216, ft1221);
				raw_term rt1224;
				rt1224.neg = false;
				rt1224.extype = raw_term::EQ;
				rt1224.e.push_back(e23);
				rt1224.e.push_back(e112);
				rt1224.e.push_back(e24);
				rt1224.calc_arity(nullptr);
				sprawformtree ft1223 = std::make_shared<raw_form_tree>(elem::NONE, rt1224);
				sprawformtree ft1214 = std::make_shared<raw_form_tree>(elem::AND, ft1215, ft1223);
				raw_term rt1226;
				rt1226.neg = false;
				rt1226.extype = raw_term::REL;
				rt1226.e.push_back(e47);
				rt1226.e.push_back(e1);
				rt1226.e.push_back(e3);
				rt1226.calc_arity(nullptr);
				sprawformtree ft1225 = std::make_shared<raw_form_tree>(elem::NONE, rt1226);
				sprawformtree ft1213 = std::make_shared<raw_form_tree>(elem::AND, ft1214, ft1225);
				raw_rule rr1227;
				rr1227.h.push_back(rt1212);
				rr1227.set_prft(ft1213);
				raw_term rt1228;
				rt1228.neg = false;
				rt1228.extype = raw_term::REL;
				rt1228.e.push_back(e70);
				rt1228.e.push_back(e1);
				rt1228.e.push_back(e2);
				rt1228.e.push_back(e239);
				rt1228.e.push_back(e3);
				rt1228.calc_arity(nullptr);
				raw_term rt1232;
				rt1232.neg = false;
				rt1232.extype = raw_term::REL;
				rt1232.e.push_back(e6);
				rt1232.e.push_back(e1);
				rt1232.e.push_back(e15);
				rt1232.e.push_back(e2);
				rt1232.e.push_back(e1144);
				rt1232.e.push_back(e1145);
				rt1232.e.push_back(e817);
				rt1232.e.push_back(e817);
				rt1232.e.push_back(e3);
				rt1232.calc_arity(nullptr);
				sprawformtree ft1231 = std::make_shared<raw_form_tree>(elem::NONE, rt1232);
				raw_term rt1234;
				rt1234.neg = false;
				rt1234.extype = raw_term::REL;
				rt1234.e.push_back(e160);
				rt1234.e.push_back(e1);
				rt1234.e.push_back(e239);
				rt1234.e.push_back(e1144);
				rt1234.e.push_back(e1145);
				rt1234.e.push_back(e3);
				rt1234.calc_arity(nullptr);
				sprawformtree ft1233 = std::make_shared<raw_form_tree>(elem::NONE, rt1234);
				sprawformtree ft1230 = std::make_shared<raw_form_tree>(elem::AND, ft1231, ft1233);
				raw_term rt1236;
				rt1236.neg = false;
				rt1236.extype = raw_term::REL;
				rt1236.e.push_back(e47);
				rt1236.e.push_back(e1);
				rt1236.e.push_back(e3);
				rt1236.calc_arity(nullptr);
				sprawformtree ft1235 = std::make_shared<raw_form_tree>(elem::NONE, rt1236);
				sprawformtree ft1229 = std::make_shared<raw_form_tree>(elem::AND, ft1230, ft1235);
				raw_rule rr1237;
				rr1237.h.push_back(rt1228);
				rr1237.set_prft(ft1229);
				raw_term rt1238;
				rt1238.neg = false;
				rt1238.extype = raw_term::REL;
				rt1238.e.push_back(e973);
				rt1238.e.push_back(e1);
				rt1238.e.push_back(e2);
				rt1238.e.push_back(e239);
				rt1238.e.push_back(e254);
				rt1238.e.push_back(e3);
				rt1238.calc_arity(nullptr);
				raw_term rt1243;
				rt1243.neg = false;
				rt1243.extype = raw_term::REL;
				rt1243.e.push_back(e6);
				rt1243.e.push_back(e1);
				rt1243.e.push_back(e34);
				rt1243.e.push_back(e2);
				rt1243.e.push_back(e3);
				rt1243.calc_arity(nullptr);
				sprawformtree ft1242 = std::make_shared<raw_form_tree>(elem::NONE, rt1243);
				raw_term rt1245;
				rt1245.neg = false;
				rt1245.extype = raw_term::REL;
				rt1245.e.push_back(e156);
				rt1245.e.push_back(e1);
				rt1245.e.push_back(e239);
				rt1245.e.push_back(e3);
				rt1245.calc_arity(nullptr);
				sprawformtree ft1244 = std::make_shared<raw_form_tree>(elem::NONE, rt1245);
				sprawformtree ft1241 = std::make_shared<raw_form_tree>(elem::AND, ft1242, ft1244);
				raw_term rt1247;
				rt1247.neg = false;
				rt1247.extype = raw_term::REL;
				rt1247.e.push_back(e156);
				rt1247.e.push_back(e1);
				rt1247.e.push_back(e254);
				rt1247.e.push_back(e3);
				rt1247.calc_arity(nullptr);
				sprawformtree ft1246 = std::make_shared<raw_form_tree>(elem::NONE, rt1247);
				sprawformtree ft1240 = std::make_shared<raw_form_tree>(elem::AND, ft1241, ft1246);
				raw_term rt1249;
				rt1249.neg = false;
				rt1249.extype = raw_term::REL;
				rt1249.e.push_back(e47);
				rt1249.e.push_back(e1);
				rt1249.e.push_back(e3);
				rt1249.calc_arity(nullptr);
				sprawformtree ft1248 = std::make_shared<raw_form_tree>(elem::NONE, rt1249);
				sprawformtree ft1239 = std::make_shared<raw_form_tree>(elem::AND, ft1240, ft1248);
				raw_rule rr1250;
				rr1250.h.push_back(rt1238);
				rr1250.set_prft(ft1239);
				raw_term rt1251;
				rt1251.neg = false;
				rt1251.extype = raw_term::REL;
				rt1251.e.push_back(e70);
				rt1251.e.push_back(e1);
				rt1251.e.push_back(e2);
				rt1251.e.push_back(e239);
				rt1251.e.push_back(e3);
				rt1251.calc_arity(nullptr);
				raw_term rt1255;
				rt1255.neg = false;
				rt1255.extype = raw_term::REL;
				rt1255.e.push_back(e6);
				rt1255.e.push_back(e1);
				rt1255.e.push_back(e34);
				rt1255.e.push_back(e2);
				rt1255.e.push_back(e3);
				rt1255.calc_arity(nullptr);
				sprawformtree ft1254 = std::make_shared<raw_form_tree>(elem::NONE, rt1255);
				raw_term rt1257;
				rt1257.neg = false;
				rt1257.extype = raw_term::REL;
				rt1257.e.push_back(e156);
				rt1257.e.push_back(e1);
				rt1257.e.push_back(e239);
				rt1257.e.push_back(e3);
				rt1257.calc_arity(nullptr);
				sprawformtree ft1256 = std::make_shared<raw_form_tree>(elem::NONE, rt1257);
				sprawformtree ft1253 = std::make_shared<raw_form_tree>(elem::AND, ft1254, ft1256);
				raw_term rt1259;
				rt1259.neg = false;
				rt1259.extype = raw_term::REL;
				rt1259.e.push_back(e47);
				rt1259.e.push_back(e1);
				rt1259.e.push_back(e3);
				rt1259.calc_arity(nullptr);
				sprawformtree ft1258 = std::make_shared<raw_form_tree>(elem::NONE, rt1259);
				sprawformtree ft1252 = std::make_shared<raw_form_tree>(elem::AND, ft1253, ft1258);
				raw_rule rr1260;
				rr1260.h.push_back(rt1251);
				rr1260.set_prft(ft1252);
				elem e1261;
				e1261.type = elem::VAR;
				e1261.e = d.get_lexeme("?as1");
				elem e1262;
				e1262.type = elem::VAR;
				e1262.e = d.get_lexeme("?as2");
				raw_term rt1263;
				rt1263.neg = false;
				rt1263.extype = raw_term::REL;
				rt1263.e.push_back(e203);
				rt1263.e.push_back(e1);
				rt1263.e.push_back(e1261);
				rt1263.e.push_back(e1262);
				rt1263.e.push_back(e3);
				rt1263.calc_arity(nullptr);
				elem e1264;
				e1264.type = elem::VAR;
				e1264.e = d.get_lexeme("?bs1");
				elem e1265;
				e1265.type = elem::VAR;
				e1265.e = d.get_lexeme("?bs2");
				raw_term rt1266;
				rt1266.neg = false;
				rt1266.extype = raw_term::REL;
				rt1266.e.push_back(e203);
				rt1266.e.push_back(e1);
				rt1266.e.push_back(e1264);
				rt1266.e.push_back(e1265);
				rt1266.e.push_back(e3);
				rt1266.calc_arity(nullptr);
				elem e1270;
				e1270.type = elem::VAR;
				e1270.e = d.get_lexeme("?e2");
				raw_term rt1271;
				rt1271.neg = false;
				rt1271.extype = raw_term::REL;
				rt1271.e.push_back(e6);
				rt1271.e.push_back(e1);
				rt1271.e.push_back(e22);
				rt1271.e.push_back(e2);
				rt1271.e.push_back(e962);
				rt1271.e.push_back(e1270);
				rt1271.e.push_back(e3);
				rt1271.calc_arity(nullptr);
				sprawformtree ft1269 = std::make_shared<raw_form_tree>(elem::NONE, rt1271);
				raw_term rt1274;
				rt1274.neg = false;
				rt1274.extype = raw_term::REL;
				rt1274.e.push_back(e973);
				rt1274.e.push_back(e1);
				rt1274.e.push_back(e962);
				rt1274.e.push_back(e1261);
				rt1274.e.push_back(e1264);
				rt1274.e.push_back(e3);
				rt1274.calc_arity(nullptr);
				sprawformtree ft1273 = std::make_shared<raw_form_tree>(elem::NONE, rt1274);
				raw_term rt1276;
				rt1276.neg = false;
				rt1276.extype = raw_term::REL;
				rt1276.e.push_back(e973);
				rt1276.e.push_back(e1);
				rt1276.e.push_back(e1270);
				rt1276.e.push_back(e1262);
				rt1276.e.push_back(e1265);
				rt1276.e.push_back(e3);
				rt1276.calc_arity(nullptr);
				sprawformtree ft1275 = std::make_shared<raw_form_tree>(elem::NONE, rt1276);
				sprawformtree ft1272 = std::make_shared<raw_form_tree>(elem::AND, ft1273, ft1275);
				sprawformtree ft1268 = std::make_shared<raw_form_tree>(elem::AND, ft1269, ft1272);
				raw_term rt1278;
				rt1278.neg = false;
				rt1278.extype = raw_term::REL;
				rt1278.e.push_back(e47);
				rt1278.e.push_back(e1);
				rt1278.e.push_back(e3);
				rt1278.calc_arity(nullptr);
				sprawformtree ft1277 = std::make_shared<raw_form_tree>(elem::NONE, rt1278);
				sprawformtree ft1267 = std::make_shared<raw_form_tree>(elem::AND, ft1268, ft1277);
				raw_rule rr1279;
				rr1279.h.push_back(rt1263);
				rr1279.h.push_back(rt1266);
				rr1279.set_prft(ft1267);
				raw_term rt1280;
				rt1280.neg = false;
				rt1280.extype = raw_term::REL;
				rt1280.e.push_back(e973);
				rt1280.e.push_back(e1);
				rt1280.e.push_back(e2);
				rt1280.e.push_back(e239);
				rt1280.e.push_back(e254);
				rt1280.e.push_back(e3);
				rt1280.calc_arity(nullptr);
				raw_term rt1286;
				rt1286.neg = false;
				rt1286.extype = raw_term::REL;
				rt1286.e.push_back(e6);
				rt1286.e.push_back(e1);
				rt1286.e.push_back(e22);
				rt1286.e.push_back(e2);
				rt1286.e.push_back(e962);
				rt1286.e.push_back(e1270);
				rt1286.e.push_back(e3);
				rt1286.calc_arity(nullptr);
				sprawformtree ft1285 = std::make_shared<raw_form_tree>(elem::NONE, rt1286);
				raw_term rt1289;
				rt1289.neg = false;
				rt1289.extype = raw_term::REL;
				rt1289.e.push_back(e973);
				rt1289.e.push_back(e1);
				rt1289.e.push_back(e962);
				rt1289.e.push_back(e1261);
				rt1289.e.push_back(e1264);
				rt1289.e.push_back(e3);
				rt1289.calc_arity(nullptr);
				sprawformtree ft1288 = std::make_shared<raw_form_tree>(elem::NONE, rt1289);
				raw_term rt1291;
				rt1291.neg = false;
				rt1291.extype = raw_term::REL;
				rt1291.e.push_back(e973);
				rt1291.e.push_back(e1);
				rt1291.e.push_back(e1270);
				rt1291.e.push_back(e1262);
				rt1291.e.push_back(e1265);
				rt1291.e.push_back(e3);
				rt1291.calc_arity(nullptr);
				sprawformtree ft1290 = std::make_shared<raw_form_tree>(elem::NONE, rt1291);
				sprawformtree ft1287 = std::make_shared<raw_form_tree>(elem::AND, ft1288, ft1290);
				sprawformtree ft1284 = std::make_shared<raw_form_tree>(elem::AND, ft1285, ft1287);
				raw_term rt1293;
				rt1293.neg = false;
				rt1293.extype = raw_term::REL;
				rt1293.e.push_back(e210);
				rt1293.e.push_back(e1);
				rt1293.e.push_back(e239);
				rt1293.e.push_back(e1261);
				rt1293.e.push_back(e1262);
				rt1293.e.push_back(e3);
				rt1293.calc_arity(nullptr);
				sprawformtree ft1292 = std::make_shared<raw_form_tree>(elem::NONE, rt1293);
				sprawformtree ft1283 = std::make_shared<raw_form_tree>(elem::AND, ft1284, ft1292);
				raw_term rt1295;
				rt1295.neg = false;
				rt1295.extype = raw_term::REL;
				rt1295.e.push_back(e210);
				rt1295.e.push_back(e1);
				rt1295.e.push_back(e254);
				rt1295.e.push_back(e1264);
				rt1295.e.push_back(e1265);
				rt1295.e.push_back(e3);
				rt1295.calc_arity(nullptr);
				sprawformtree ft1294 = std::make_shared<raw_form_tree>(elem::NONE, rt1295);
				sprawformtree ft1282 = std::make_shared<raw_form_tree>(elem::AND, ft1283, ft1294);
				raw_term rt1297;
				rt1297.neg = false;
				rt1297.extype = raw_term::REL;
				rt1297.e.push_back(e47);
				rt1297.e.push_back(e1);
				rt1297.e.push_back(e3);
				rt1297.calc_arity(nullptr);
				sprawformtree ft1296 = std::make_shared<raw_form_tree>(elem::NONE, rt1297);
				sprawformtree ft1281 = std::make_shared<raw_form_tree>(elem::AND, ft1282, ft1296);
				raw_rule rr1298;
				rr1298.h.push_back(rt1280);
				rr1298.set_prft(ft1281);
				raw_term rt1299;
				rt1299.neg = false;
				rt1299.extype = raw_term::REL;
				rt1299.e.push_back(e203);
				rt1299.e.push_back(e1);
				rt1299.e.push_back(e1261);
				rt1299.e.push_back(e1262);
				rt1299.e.push_back(e3);
				rt1299.calc_arity(nullptr);
				raw_term rt1304;
				rt1304.neg = false;
				rt1304.extype = raw_term::REL;
				rt1304.e.push_back(e6);
				rt1304.e.push_back(e1);
				rt1304.e.push_back(e22);
				rt1304.e.push_back(e2);
				rt1304.e.push_back(e962);
				rt1304.e.push_back(e1270);
				rt1304.e.push_back(e3);
				rt1304.calc_arity(nullptr);
				sprawformtree ft1303 = std::make_shared<raw_form_tree>(elem::NONE, rt1304);
				raw_term rt1306;
				rt1306.neg = false;
				rt1306.extype = raw_term::REL;
				rt1306.e.push_back(e70);
				rt1306.e.push_back(e1);
				rt1306.e.push_back(e962);
				rt1306.e.push_back(e1261);
				rt1306.e.push_back(e3);
				rt1306.calc_arity(nullptr);
				sprawformtree ft1305 = std::make_shared<raw_form_tree>(elem::NONE, rt1306);
				sprawformtree ft1302 = std::make_shared<raw_form_tree>(elem::AND, ft1303, ft1305);
				raw_term rt1308;
				rt1308.neg = false;
				rt1308.extype = raw_term::REL;
				rt1308.e.push_back(e70);
				rt1308.e.push_back(e1);
				rt1308.e.push_back(e1270);
				rt1308.e.push_back(e1262);
				rt1308.e.push_back(e3);
				rt1308.calc_arity(nullptr);
				sprawformtree ft1307 = std::make_shared<raw_form_tree>(elem::NONE, rt1308);
				sprawformtree ft1301 = std::make_shared<raw_form_tree>(elem::AND, ft1302, ft1307);
				raw_term rt1310;
				rt1310.neg = false;
				rt1310.extype = raw_term::REL;
				rt1310.e.push_back(e47);
				rt1310.e.push_back(e1);
				rt1310.e.push_back(e3);
				rt1310.calc_arity(nullptr);
				sprawformtree ft1309 = std::make_shared<raw_form_tree>(elem::NONE, rt1310);
				sprawformtree ft1300 = std::make_shared<raw_form_tree>(elem::AND, ft1301, ft1309);
				raw_rule rr1311;
				rr1311.h.push_back(rt1299);
				rr1311.set_prft(ft1300);
				raw_term rt1312;
				rt1312.neg = false;
				rt1312.extype = raw_term::REL;
				rt1312.e.push_back(e70);
				rt1312.e.push_back(e1);
				rt1312.e.push_back(e2);
				rt1312.e.push_back(e239);
				rt1312.e.push_back(e3);
				rt1312.calc_arity(nullptr);
				raw_term rt1318;
				rt1318.neg = false;
				rt1318.extype = raw_term::REL;
				rt1318.e.push_back(e6);
				rt1318.e.push_back(e1);
				rt1318.e.push_back(e22);
				rt1318.e.push_back(e2);
				rt1318.e.push_back(e962);
				rt1318.e.push_back(e1270);
				rt1318.e.push_back(e3);
				rt1318.calc_arity(nullptr);
				sprawformtree ft1317 = std::make_shared<raw_form_tree>(elem::NONE, rt1318);
				raw_term rt1320;
				rt1320.neg = false;
				rt1320.extype = raw_term::REL;
				rt1320.e.push_back(e70);
				rt1320.e.push_back(e1);
				rt1320.e.push_back(e962);
				rt1320.e.push_back(e1261);
				rt1320.e.push_back(e3);
				rt1320.calc_arity(nullptr);
				sprawformtree ft1319 = std::make_shared<raw_form_tree>(elem::NONE, rt1320);
				sprawformtree ft1316 = std::make_shared<raw_form_tree>(elem::AND, ft1317, ft1319);
				raw_term rt1322;
				rt1322.neg = false;
				rt1322.extype = raw_term::REL;
				rt1322.e.push_back(e70);
				rt1322.e.push_back(e1);
				rt1322.e.push_back(e1270);
				rt1322.e.push_back(e1262);
				rt1322.e.push_back(e3);
				rt1322.calc_arity(nullptr);
				sprawformtree ft1321 = std::make_shared<raw_form_tree>(elem::NONE, rt1322);
				sprawformtree ft1315 = std::make_shared<raw_form_tree>(elem::AND, ft1316, ft1321);
				raw_term rt1324;
				rt1324.neg = false;
				rt1324.extype = raw_term::REL;
				rt1324.e.push_back(e210);
				rt1324.e.push_back(e1);
				rt1324.e.push_back(e239);
				rt1324.e.push_back(e1261);
				rt1324.e.push_back(e1262);
				rt1324.e.push_back(e3);
				rt1324.calc_arity(nullptr);
				sprawformtree ft1323 = std::make_shared<raw_form_tree>(elem::NONE, rt1324);
				sprawformtree ft1314 = std::make_shared<raw_form_tree>(elem::AND, ft1315, ft1323);
				raw_term rt1326;
				rt1326.neg = false;
				rt1326.extype = raw_term::REL;
				rt1326.e.push_back(e47);
				rt1326.e.push_back(e1);
				rt1326.e.push_back(e3);
				rt1326.calc_arity(nullptr);
				sprawformtree ft1325 = std::make_shared<raw_form_tree>(elem::NONE, rt1326);
				sprawformtree ft1313 = std::make_shared<raw_form_tree>(elem::AND, ft1314, ft1325);
				raw_rule rr1327;
				rr1327.h.push_back(rt1312);
				rr1327.set_prft(ft1313);
				raw_term rt1328;
				rt1328.neg = false;
				rt1328.extype = raw_term::REL;
				rt1328.e.push_back(e203);
				rt1328.e.push_back(e1);
				rt1328.e.push_back(e1261);
				rt1328.e.push_back(e1262);
				rt1328.e.push_back(e3);
				rt1328.calc_arity(nullptr);
				raw_term rt1329;
				rt1329.neg = false;
				rt1329.extype = raw_term::REL;
				rt1329.e.push_back(e203);
				rt1329.e.push_back(e1);
				rt1329.e.push_back(e1264);
				rt1329.e.push_back(e1265);
				rt1329.e.push_back(e3);
				rt1329.calc_arity(nullptr);
				raw_term rt1333;
				rt1333.neg = false;
				rt1333.extype = raw_term::REL;
				rt1333.e.push_back(e6);
				rt1333.e.push_back(e1);
				rt1333.e.push_back(e29);
				rt1333.e.push_back(e2);
				rt1333.e.push_back(e962);
				rt1333.e.push_back(e1270);
				rt1333.e.push_back(e3);
				rt1333.calc_arity(nullptr);
				sprawformtree ft1332 = std::make_shared<raw_form_tree>(elem::NONE, rt1333);
				raw_term rt1336;
				rt1336.neg = false;
				rt1336.extype = raw_term::REL;
				rt1336.e.push_back(e973);
				rt1336.e.push_back(e1);
				rt1336.e.push_back(e962);
				rt1336.e.push_back(e1261);
				rt1336.e.push_back(e1264);
				rt1336.e.push_back(e3);
				rt1336.calc_arity(nullptr);
				sprawformtree ft1335 = std::make_shared<raw_form_tree>(elem::NONE, rt1336);
				raw_term rt1338;
				rt1338.neg = false;
				rt1338.extype = raw_term::REL;
				rt1338.e.push_back(e973);
				rt1338.e.push_back(e1);
				rt1338.e.push_back(e1270);
				rt1338.e.push_back(e1262);
				rt1338.e.push_back(e1265);
				rt1338.e.push_back(e3);
				rt1338.calc_arity(nullptr);
				sprawformtree ft1337 = std::make_shared<raw_form_tree>(elem::NONE, rt1338);
				sprawformtree ft1334 = std::make_shared<raw_form_tree>(elem::AND, ft1335, ft1337);
				sprawformtree ft1331 = std::make_shared<raw_form_tree>(elem::AND, ft1332, ft1334);
				raw_term rt1340;
				rt1340.neg = false;
				rt1340.extype = raw_term::REL;
				rt1340.e.push_back(e47);
				rt1340.e.push_back(e1);
				rt1340.e.push_back(e3);
				rt1340.calc_arity(nullptr);
				sprawformtree ft1339 = std::make_shared<raw_form_tree>(elem::NONE, rt1340);
				sprawformtree ft1330 = std::make_shared<raw_form_tree>(elem::AND, ft1331, ft1339);
				raw_rule rr1341;
				rr1341.h.push_back(rt1328);
				rr1341.h.push_back(rt1329);
				rr1341.set_prft(ft1330);
				raw_term rt1342;
				rt1342.neg = false;
				rt1342.extype = raw_term::REL;
				rt1342.e.push_back(e973);
				rt1342.e.push_back(e1);
				rt1342.e.push_back(e2);
				rt1342.e.push_back(e239);
				rt1342.e.push_back(e254);
				rt1342.e.push_back(e3);
				rt1342.calc_arity(nullptr);
				raw_term rt1348;
				rt1348.neg = false;
				rt1348.extype = raw_term::REL;
				rt1348.e.push_back(e6);
				rt1348.e.push_back(e1);
				rt1348.e.push_back(e29);
				rt1348.e.push_back(e2);
				rt1348.e.push_back(e962);
				rt1348.e.push_back(e1270);
				rt1348.e.push_back(e3);
				rt1348.calc_arity(nullptr);
				sprawformtree ft1347 = std::make_shared<raw_form_tree>(elem::NONE, rt1348);
				raw_term rt1351;
				rt1351.neg = false;
				rt1351.extype = raw_term::REL;
				rt1351.e.push_back(e973);
				rt1351.e.push_back(e1);
				rt1351.e.push_back(e962);
				rt1351.e.push_back(e1261);
				rt1351.e.push_back(e1264);
				rt1351.e.push_back(e3);
				rt1351.calc_arity(nullptr);
				sprawformtree ft1350 = std::make_shared<raw_form_tree>(elem::NONE, rt1351);
				raw_term rt1353;
				rt1353.neg = false;
				rt1353.extype = raw_term::REL;
				rt1353.e.push_back(e973);
				rt1353.e.push_back(e1);
				rt1353.e.push_back(e1270);
				rt1353.e.push_back(e1262);
				rt1353.e.push_back(e1265);
				rt1353.e.push_back(e3);
				rt1353.calc_arity(nullptr);
				sprawformtree ft1352 = std::make_shared<raw_form_tree>(elem::NONE, rt1353);
				sprawformtree ft1349 = std::make_shared<raw_form_tree>(elem::ALT, ft1350, ft1352);
				sprawformtree ft1346 = std::make_shared<raw_form_tree>(elem::AND, ft1347, ft1349);
				raw_term rt1355;
				rt1355.neg = false;
				rt1355.extype = raw_term::REL;
				rt1355.e.push_back(e210);
				rt1355.e.push_back(e1);
				rt1355.e.push_back(e239);
				rt1355.e.push_back(e1261);
				rt1355.e.push_back(e1262);
				rt1355.e.push_back(e3);
				rt1355.calc_arity(nullptr);
				sprawformtree ft1354 = std::make_shared<raw_form_tree>(elem::NONE, rt1355);
				sprawformtree ft1345 = std::make_shared<raw_form_tree>(elem::AND, ft1346, ft1354);
				raw_term rt1357;
				rt1357.neg = false;
				rt1357.extype = raw_term::REL;
				rt1357.e.push_back(e210);
				rt1357.e.push_back(e1);
				rt1357.e.push_back(e254);
				rt1357.e.push_back(e1264);
				rt1357.e.push_back(e1265);
				rt1357.e.push_back(e3);
				rt1357.calc_arity(nullptr);
				sprawformtree ft1356 = std::make_shared<raw_form_tree>(elem::NONE, rt1357);
				sprawformtree ft1344 = std::make_shared<raw_form_tree>(elem::AND, ft1345, ft1356);
				raw_term rt1359;
				rt1359.neg = false;
				rt1359.extype = raw_term::REL;
				rt1359.e.push_back(e47);
				rt1359.e.push_back(e1);
				rt1359.e.push_back(e3);
				rt1359.calc_arity(nullptr);
				sprawformtree ft1358 = std::make_shared<raw_form_tree>(elem::NONE, rt1359);
				sprawformtree ft1343 = std::make_shared<raw_form_tree>(elem::AND, ft1344, ft1358);
				raw_rule rr1360;
				rr1360.h.push_back(rt1342);
				rr1360.set_prft(ft1343);
				raw_term rt1361;
				rt1361.neg = false;
				rt1361.extype = raw_term::REL;
				rt1361.e.push_back(e203);
				rt1361.e.push_back(e1);
				rt1361.e.push_back(e1261);
				rt1361.e.push_back(e1262);
				rt1361.e.push_back(e3);
				rt1361.calc_arity(nullptr);
				raw_term rt1366;
				rt1366.neg = false;
				rt1366.extype = raw_term::REL;
				rt1366.e.push_back(e6);
				rt1366.e.push_back(e1);
				rt1366.e.push_back(e29);
				rt1366.e.push_back(e2);
				rt1366.e.push_back(e962);
				rt1366.e.push_back(e1270);
				rt1366.e.push_back(e3);
				rt1366.calc_arity(nullptr);
				sprawformtree ft1365 = std::make_shared<raw_form_tree>(elem::NONE, rt1366);
				raw_term rt1368;
				rt1368.neg = false;
				rt1368.extype = raw_term::REL;
				rt1368.e.push_back(e70);
				rt1368.e.push_back(e1);
				rt1368.e.push_back(e962);
				rt1368.e.push_back(e1261);
				rt1368.e.push_back(e3);
				rt1368.calc_arity(nullptr);
				sprawformtree ft1367 = std::make_shared<raw_form_tree>(elem::NONE, rt1368);
				sprawformtree ft1364 = std::make_shared<raw_form_tree>(elem::AND, ft1365, ft1367);
				raw_term rt1370;
				rt1370.neg = false;
				rt1370.extype = raw_term::REL;
				rt1370.e.push_back(e70);
				rt1370.e.push_back(e1);
				rt1370.e.push_back(e1270);
				rt1370.e.push_back(e1262);
				rt1370.e.push_back(e3);
				rt1370.calc_arity(nullptr);
				sprawformtree ft1369 = std::make_shared<raw_form_tree>(elem::NONE, rt1370);
				sprawformtree ft1363 = std::make_shared<raw_form_tree>(elem::AND, ft1364, ft1369);
				raw_term rt1372;
				rt1372.neg = false;
				rt1372.extype = raw_term::REL;
				rt1372.e.push_back(e47);
				rt1372.e.push_back(e1);
				rt1372.e.push_back(e3);
				rt1372.calc_arity(nullptr);
				sprawformtree ft1371 = std::make_shared<raw_form_tree>(elem::NONE, rt1372);
				sprawformtree ft1362 = std::make_shared<raw_form_tree>(elem::AND, ft1363, ft1371);
				raw_rule rr1373;
				rr1373.h.push_back(rt1361);
				rr1373.set_prft(ft1362);
				raw_term rt1374;
				rt1374.neg = false;
				rt1374.extype = raw_term::REL;
				rt1374.e.push_back(e70);
				rt1374.e.push_back(e1);
				rt1374.e.push_back(e2);
				rt1374.e.push_back(e239);
				rt1374.e.push_back(e3);
				rt1374.calc_arity(nullptr);
				raw_term rt1380;
				rt1380.neg = false;
				rt1380.extype = raw_term::REL;
				rt1380.e.push_back(e6);
				rt1380.e.push_back(e1);
				rt1380.e.push_back(e29);
				rt1380.e.push_back(e2);
				rt1380.e.push_back(e962);
				rt1380.e.push_back(e1270);
				rt1380.e.push_back(e3);
				rt1380.calc_arity(nullptr);
				sprawformtree ft1379 = std::make_shared<raw_form_tree>(elem::NONE, rt1380);
				raw_term rt1382;
				rt1382.neg = false;
				rt1382.extype = raw_term::REL;
				rt1382.e.push_back(e70);
				rt1382.e.push_back(e1);
				rt1382.e.push_back(e962);
				rt1382.e.push_back(e1261);
				rt1382.e.push_back(e3);
				rt1382.calc_arity(nullptr);
				sprawformtree ft1381 = std::make_shared<raw_form_tree>(elem::NONE, rt1382);
				sprawformtree ft1378 = std::make_shared<raw_form_tree>(elem::AND, ft1379, ft1381);
				raw_term rt1384;
				rt1384.neg = false;
				rt1384.extype = raw_term::REL;
				rt1384.e.push_back(e70);
				rt1384.e.push_back(e1);
				rt1384.e.push_back(e1270);
				rt1384.e.push_back(e1262);
				rt1384.e.push_back(e3);
				rt1384.calc_arity(nullptr);
				sprawformtree ft1383 = std::make_shared<raw_form_tree>(elem::NONE, rt1384);
				sprawformtree ft1377 = std::make_shared<raw_form_tree>(elem::AND, ft1378, ft1383);
				raw_term rt1386;
				rt1386.neg = false;
				rt1386.extype = raw_term::REL;
				rt1386.e.push_back(e210);
				rt1386.e.push_back(e1);
				rt1386.e.push_back(e239);
				rt1386.e.push_back(e1261);
				rt1386.e.push_back(e1262);
				rt1386.e.push_back(e3);
				rt1386.calc_arity(nullptr);
				sprawformtree ft1385 = std::make_shared<raw_form_tree>(elem::NONE, rt1386);
				sprawformtree ft1376 = std::make_shared<raw_form_tree>(elem::AND, ft1377, ft1385);
				raw_term rt1388;
				rt1388.neg = false;
				rt1388.extype = raw_term::REL;
				rt1388.e.push_back(e47);
				rt1388.e.push_back(e1);
				rt1388.e.push_back(e3);
				rt1388.calc_arity(nullptr);
				sprawformtree ft1387 = std::make_shared<raw_form_tree>(elem::NONE, rt1388);
				sprawformtree ft1375 = std::make_shared<raw_form_tree>(elem::AND, ft1376, ft1387);
				raw_rule rr1389;
				rr1389.h.push_back(rt1374);
				rr1389.set_prft(ft1375);
				raw_prog &rp1390 = rp;
				rp1390.r.push_back(rr12);
				rp1390.r.push_back(rr19);
				rp1390.r.push_back(rr26);
				rp1390.r.push_back(rr31);
				rp1390.r.push_back(rr36);
				rp1390.r.push_back(rr44);
				rp1390.r.push_back(rr72);
				rp1390.r.push_back(rr77);
				rp1390.r.push_back(rr81);
				rp1390.r.push_back(rr99);
				rp1390.r.push_back(rr103);
				rp1390.r.push_back(rr107);
				rp1390.r.push_back(rr114);
				rp1390.r.push_back(rr119);
				rp1390.r.push_back(rr124);
				rp1390.r.push_back(rr129);
				rp1390.r.push_back(rr134);
				rp1390.r.push_back(rr139);
				rp1390.r.push_back(rr144);
				rp1390.r.push_back(rr152);
				rp1390.r.push_back(rr159);
				rp1390.r.push_back(rr164);
				rp1390.r.push_back(rr173);
				rp1390.r.push_back(rr180);
				rp1390.r.push_back(rr188);
				rp1390.r.push_back(rr196);
				rp1390.r.push_back(rr212);
				rp1390.r.push_back(rr233);
				rp1390.r.push_back(rr248);
				rp1390.r.push_back(rr252);
				rp1390.r.push_back(rr268);
				rp1390.r.push_back(rr288);
				rp1390.r.push_back(rr301);
				rp1390.r.push_back(rr305);
				rp1390.r.push_back(rr322);
				rp1390.r.push_back(rr343);
				rp1390.r.push_back(rr363);
				rp1390.r.push_back(rr388);
				rp1390.r.push_back(rr412);
				rp1390.r.push_back(rr432);
				rp1390.r.push_back(rr455);
				rp1390.r.push_back(rr463);
				rp1390.r.push_back(rr480);
				rp1390.r.push_back(rr498);
				rp1390.r.push_back(rr519);
				rp1390.r.push_back(rr534);
				rp1390.r.push_back(rr550);
				rp1390.r.push_back(rr556);
				rp1390.r.push_back(rr572);
				rp1390.r.push_back(rr590);
				rp1390.r.push_back(rr613);
				rp1390.r.push_back(rr636);
				rp1390.r.push_back(rr654);
				rp1390.r.push_back(rr661);
				rp1390.r.push_back(rr681);
				rp1390.r.push_back(rr705);
				rp1390.r.push_back(rr730);
				rp1390.r.push_back(rr755);
				rp1390.r.push_back(rr777);
				rp1390.r.push_back(rr787);
				rp1390.r.push_back(rr803);
				rp1390.r.push_back(rr826);
				rp1390.r.push_back(rr842);
				rp1390.r.push_back(rr860);
				rp1390.r.push_back(rr868);
				rp1390.r.push_back(rr873);
				rp1390.r.push_back(rr889);
				rp1390.r.push_back(rr908);
				rp1390.r.push_back(rr924);
				rp1390.r.push_back(rr942);
				rp1390.r.push_back(rr949);
				rp1390.r.push_back(rr954);
				rp1390.r.push_back(rr980);
				rp1390.r.push_back(rr999);
				rp1390.r.push_back(rr1016);
				rp1390.r.push_back(rr1046);
				rp1390.r.push_back(rr1073);
				rp1390.r.push_back(rr1086);
				rp1390.r.push_back(rr1099);
				rp1390.r.push_back(rr1114);
				rp1390.r.push_back(rr1137);
				rp1390.r.push_back(rr1155);
				rp1390.r.push_back(rr1165);
				rp1390.r.push_back(rr1178);
				rp1390.r.push_back(rr1188);
				rp1390.r.push_back(rr1201);
				rp1390.r.push_back(rr1211);
				rp1390.r.push_back(rr1227);
				rp1390.r.push_back(rr1237);
				rp1390.r.push_back(rr1250);
				rp1390.r.push_back(rr1260);
				rp1390.r.push_back(rr1279);
				rp1390.r.push_back(rr1298);
				rp1390.r.push_back(rr1311);
				rp1390.r.push_back(rr1327);
				rp1390.r.push_back(rr1341);
				rp1390.r.push_back(rr1360);
				rp1390.r.push_back(rr1373);
				rp1390.r.push_back(rr1389);
			}
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

/* Converts a pure TML program into one that uses no conjunctions. Does
 * this using the formula a & b = ~((~a) | (~b)). More concretely,
 * for each conjunct, creates a disjunction of a rule predicated on its
 * negation, and then defines the original rule as the negation of this
 * disjunction. */

void driver::unary_transform(raw_prog &rp) {
	// Get dictionary for generating fresh symbols
	dict_t &d = tbl->get_dict();
	// The vector in which pending dijuncts are temporarily stored
	std::vector<raw_rule> pending_rules;
	// Convert each rule with multiple conjuncts into multiple unary rules
	for(raw_rule &rr : rp.r) {
		if(rr.b.size() == 1 && rr.b[0].size() > 1) {
			raw_term neg_head(elem::fresh_temp_sym(d), collect_free_vars(rr));
			// Make each disjunct of the negation of the current rule
			for(raw_term &rt : rr.b[0]) {
				pending_rules.push_back(raw_rule(neg_head, { rt.negate() }));
			}
			// Recover the original rule by negating the negation
			rr.set_b({{ neg_head.negate() }});
		}
	}
	// Finally add pending rules without risk of interfering with iterator
	for(raw_rule &rr : pending_rules) {
		rp.r.push_back(rr);
	}
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
	
	std::map<elem, elem> freeze_map;
	std::map<elem, elem> unfreeze_map;
	// Separate the internal rules used to execute the parts of the
	// transformation from the external rules used to expose the results
	// of computation.
	std::vector<raw_rule> ext_prog, int_prog;
	// Create a duplicate of each rule in the given program under a
	// generated alias.
	for(raw_rule rr : rp.r) {
		for(raw_term &rt : rr.h) {
			raw_term rt2 = rt;
			auto it = freeze_map.find(rt.e[0]);
			if(it != freeze_map.end()) {
				rt.e[0] = it->second;
			} else {
				elem frozen_elem = elem::fresh_temp_sym(d);
				// Store the mapping so that the derived portion of each
				// relation is stored in exactly one place
				unfreeze_map[frozen_elem] = rt.e[0];
				rt.e[0] = freeze_map[rt.e[0]] = frozen_elem;
			}
			// Update the external interface
			raw_term rt1 = rt;
			rt2.neg = rt1.neg = false;
			ext_prog.push_back(raw_rule(rt2, rt1));
			rt2.neg = rt1.neg = true;
			ext_prog.push_back(raw_rule(rt2, rt1));
		}
		int_prog.push_back(rr);
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
				// If the present relation does not correspond to a relation in
				// the original program, then clear the table so it does not
				// affect future stages.
				if(unfreeze_map.find(general_head.e[0]) == unfreeze_map.end()) {
					rp.r.push_back(raw_rule(general_head.negate(),
						{ general_head, raw_term(clock_states[0], std::vector<elem>{}) }));
				}
				for(raw_rule rr : *w) {
					// Condition everything in the current stage with the same
					// clock state
					rp.r.push_back(condition_rule(rr,
						raw_term(clock_state, std::vector<elem>{})));
				}
			}
		}
		// Start the clock ticking by asserting stage0, asserting stage1
		// if stage0 holds, and asserting the clock if stage0 holds but
		// stage1 does not.
		raw_term stage0(elem::fresh_temp_sym(d), std::vector<elem>{});
		raw_term stage1(elem::fresh_temp_sym(d), std::vector<elem>{});
		raw_term stage2(clock_states[0], std::vector<elem>{});
		rp.r.push_back(raw_rule(stage0));
		rp.r.push_back(raw_rule(stage1, stage0));
		rp.r.push_back(raw_rule(stage2, {stage0, stage1.negate()}));
		
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
	} else {
		// If there are no interdepencies then we can just restore the
		// original rule names to the transformed program
		for(raw_rule &rr : rp.r) {
			for(raw_term &rt : rr.h) {
				auto jt = unfreeze_map.find(rt.e[0]);
				if(jt != unfreeze_map.end()) {
					rt.e[0] = jt->second;
				}
			}
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
		prog_constr += e_name + to_string_t(".e = ") + dict_name + to_string_t(".get_lexeme(\"") + lexeme2str(e.e) + to_string_t("\");\n");
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
		transform_domains(rp);
		transform_quotes(rp);
		std::cout << "Quoted Program:" << std::endl << std::endl << rp << std::endl;
		transform_evals(rp);
		std::cout << "Evaled Program:" << std::endl << std::endl << rp << std::endl;
		//quote_prog(rp, elem(elem::SYM, get_lexeme("this")), rp);
		//std::cout << "TML Program With this:" << std::endl << std::endl << rp << std::endl;
		step_transform(rp, [&](raw_prog &rp) {
			to_pure_tml(rp);
			unary_transform(rp);
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
