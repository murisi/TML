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
				e150.e = d.get_lexeme("LST");
				elem e151;
				e151.type = elem::VAR;
				e151.e = d.get_lexeme("?a");
				elem e152;
				e152.type = elem::VAR;
				e152.e = d.get_lexeme("?c");
				raw_term rt153;
				rt153.neg = false;
				rt153.extype = raw_term::REL;
				rt153.e.push_back(e150);
				rt153.e.push_back(e1);
				rt153.e.push_back(e151);
				rt153.e.push_back(e39);
				rt153.e.push_back(e152);
				rt153.e.push_back(e3);
				rt153.calc_arity(nullptr);
				elem &e155 = domain_sym;
				raw_term rt156;
				rt156.neg = false;
				rt156.extype = raw_term::REL;
				rt156.e.push_back(e155);
				rt156.e.push_back(e1);
				rt156.e.push_back(e151);
				rt156.e.push_back(e39);
				rt156.e.push_back(e152);
				rt156.e.push_back(e3);
				rt156.calc_arity(nullptr);
				sprawformtree ft154 = std::make_shared<raw_form_tree>(elem::NONE, rt156);
				raw_rule rr157;
				rr157.h.push_back(rt153);
				rr157.set_prft(ft154);
				elem e158;
				e158.type = elem::SYM;
				e158.e = d.get_lexeme("DOMAIN");
				raw_term rt159;
				rt159.neg = false;
				rt159.extype = raw_term::REL;
				rt159.e.push_back(e158);
				rt159.e.push_back(e1);
				rt159.e.push_back(e59);
				rt159.e.push_back(e3);
				rt159.calc_arity(nullptr);
				elem e161;
				e161.type = elem::VAR;
				e161.e = d.get_lexeme("?w");
				raw_term rt162;
				rt162.neg = false;
				rt162.extype = raw_term::REL;
				rt162.e.push_back(e155);
				rt162.e.push_back(e1);
				rt162.e.push_back(e161);
				rt162.e.push_back(e59);
				rt162.e.push_back(e47);
				rt162.e.push_back(e3);
				rt162.calc_arity(nullptr);
				sprawformtree ft160 = std::make_shared<raw_form_tree>(elem::NONE, rt162);
				raw_rule rr163;
				rr163.h.push_back(rt159);
				rr163.set_prft(ft160);
				elem e164;
				e164.type = elem::SYM;
				e164.e = d.get_lexeme("LIST_CONS");
				raw_term rt165;
				rt165.neg = false;
				rt165.extype = raw_term::REL;
				rt165.e.push_back(e164);
				rt165.e.push_back(e1);
				rt165.e.push_back(e2);
				rt165.e.push_back(e3);
				rt165.calc_arity(nullptr);
				raw_term rt167;
				rt167.neg = false;
				rt167.extype = raw_term::REL;
				rt167.e.push_back(e155);
				rt167.e.push_back(e1);
				rt167.e.push_back(e2);
				rt167.e.push_back(e3);
				rt167.calc_arity(nullptr);
				sprawformtree ft166 = std::make_shared<raw_form_tree>(elem::NONE, rt167);
				raw_rule rr168;
				rr168.h.push_back(rt165);
				rr168.set_prft(ft166);
				raw_term rt169;
				rt169.neg = false;
				rt169.extype = raw_term::REL;
				rt169.e.push_back(e164);
				rt169.e.push_back(e1);
				rt169.e.push_back(e2);
				rt169.e.push_back(e151);
				rt169.e.push_back(e3);
				rt169.calc_arity(nullptr);
				elem e172;
				e172.type = elem::VAR;
				e172.e = d.get_lexeme("?rst");
				raw_term rt173;
				rt173.neg = false;
				rt173.extype = raw_term::REL;
				rt173.e.push_back(e155);
				rt173.e.push_back(e1);
				rt173.e.push_back(e2);
				rt173.e.push_back(e151);
				rt173.e.push_back(e172);
				rt173.e.push_back(e3);
				rt173.calc_arity(nullptr);
				sprawformtree ft171 = std::make_shared<raw_form_tree>(elem::NONE, rt173);
				raw_term rt175;
				rt175.neg = false;
				rt175.extype = raw_term::REL;
				rt175.e.push_back(e164);
				rt175.e.push_back(e1);
				rt175.e.push_back(e172);
				rt175.e.push_back(e3);
				rt175.calc_arity(nullptr);
				sprawformtree ft174 = std::make_shared<raw_form_tree>(elem::NONE, rt175);
				sprawformtree ft170 = std::make_shared<raw_form_tree>(elem::AND, ft171, ft174);
				raw_rule rr176;
				rr176.h.push_back(rt169);
				rr176.set_prft(ft170);
				raw_term rt177;
				rt177.neg = false;
				rt177.extype = raw_term::REL;
				rt177.e.push_back(e164);
				rt177.e.push_back(e1);
				rt177.e.push_back(e2);
				rt177.e.push_back(e151);
				rt177.e.push_back(e39);
				rt177.e.push_back(e3);
				rt177.calc_arity(nullptr);
				raw_term rt180;
				rt180.neg = false;
				rt180.extype = raw_term::REL;
				rt180.e.push_back(e155);
				rt180.e.push_back(e1);
				rt180.e.push_back(e2);
				rt180.e.push_back(e151);
				rt180.e.push_back(e172);
				rt180.e.push_back(e3);
				rt180.calc_arity(nullptr);
				sprawformtree ft179 = std::make_shared<raw_form_tree>(elem::NONE, rt180);
				raw_term rt182;
				rt182.neg = false;
				rt182.extype = raw_term::REL;
				rt182.e.push_back(e164);
				rt182.e.push_back(e1);
				rt182.e.push_back(e172);
				rt182.e.push_back(e39);
				rt182.e.push_back(e3);
				rt182.calc_arity(nullptr);
				sprawformtree ft181 = std::make_shared<raw_form_tree>(elem::NONE, rt182);
				sprawformtree ft178 = std::make_shared<raw_form_tree>(elem::AND, ft179, ft181);
				raw_rule rr183;
				rr183.h.push_back(rt177);
				rr183.set_prft(ft178);
				raw_term rt184;
				rt184.neg = false;
				rt184.extype = raw_term::REL;
				rt184.e.push_back(e164);
				rt184.e.push_back(e1);
				rt184.e.push_back(e2);
				rt184.e.push_back(e151);
				rt184.e.push_back(e39);
				rt184.e.push_back(e152);
				rt184.e.push_back(e3);
				rt184.calc_arity(nullptr);
				raw_term rt187;
				rt187.neg = false;
				rt187.extype = raw_term::REL;
				rt187.e.push_back(e155);
				rt187.e.push_back(e1);
				rt187.e.push_back(e2);
				rt187.e.push_back(e151);
				rt187.e.push_back(e172);
				rt187.e.push_back(e3);
				rt187.calc_arity(nullptr);
				sprawformtree ft186 = std::make_shared<raw_form_tree>(elem::NONE, rt187);
				raw_term rt189;
				rt189.neg = false;
				rt189.extype = raw_term::REL;
				rt189.e.push_back(e164);
				rt189.e.push_back(e1);
				rt189.e.push_back(e172);
				rt189.e.push_back(e39);
				rt189.e.push_back(e152);
				rt189.e.push_back(e3);
				rt189.calc_arity(nullptr);
				sprawformtree ft188 = std::make_shared<raw_form_tree>(elem::NONE, rt189);
				sprawformtree ft185 = std::make_shared<raw_form_tree>(elem::AND, ft186, ft188);
				raw_rule rr190;
				rr190.h.push_back(rt184);
				rr190.set_prft(ft185);
				elem e191;
				e191.type = elem::VAR;
				e191.e = d.get_lexeme("?d");
				raw_term rt192;
				rt192.neg = false;
				rt192.extype = raw_term::REL;
				rt192.e.push_back(e164);
				rt192.e.push_back(e1);
				rt192.e.push_back(e2);
				rt192.e.push_back(e151);
				rt192.e.push_back(e39);
				rt192.e.push_back(e152);
				rt192.e.push_back(e191);
				rt192.e.push_back(e3);
				rt192.calc_arity(nullptr);
				raw_term rt195;
				rt195.neg = false;
				rt195.extype = raw_term::REL;
				rt195.e.push_back(e155);
				rt195.e.push_back(e1);
				rt195.e.push_back(e2);
				rt195.e.push_back(e151);
				rt195.e.push_back(e172);
				rt195.e.push_back(e3);
				rt195.calc_arity(nullptr);
				sprawformtree ft194 = std::make_shared<raw_form_tree>(elem::NONE, rt195);
				raw_term rt197;
				rt197.neg = false;
				rt197.extype = raw_term::REL;
				rt197.e.push_back(e164);
				rt197.e.push_back(e1);
				rt197.e.push_back(e172);
				rt197.e.push_back(e39);
				rt197.e.push_back(e152);
				rt197.e.push_back(e191);
				rt197.e.push_back(e3);
				rt197.calc_arity(nullptr);
				sprawformtree ft196 = std::make_shared<raw_form_tree>(elem::NONE, rt197);
				sprawformtree ft193 = std::make_shared<raw_form_tree>(elem::AND, ft194, ft196);
				raw_rule rr198;
				rr198.h.push_back(rt192);
				rr198.set_prft(ft193);
				elem e199;
				e199.type = elem::SYM;
				e199.e = d.get_lexeme("LIST_LST");
				raw_term rt200;
				rt200.neg = false;
				rt200.extype = raw_term::REL;
				rt200.e.push_back(e199);
				rt200.e.push_back(e1);
				rt200.e.push_back(e2);
				rt200.e.push_back(e3);
				rt200.calc_arity(nullptr);
				raw_term rt202;
				rt202.neg = false;
				rt202.extype = raw_term::REL;
				rt202.e.push_back(e150);
				rt202.e.push_back(e1);
				rt202.e.push_back(e2);
				rt202.e.push_back(e3);
				rt202.calc_arity(nullptr);
				sprawformtree ft201 = std::make_shared<raw_form_tree>(elem::NONE, rt202);
				raw_rule rr203;
				rr203.h.push_back(rt200);
				rr203.set_prft(ft201);
				raw_term rt204;
				rt204.neg = false;
				rt204.extype = raw_term::REL;
				rt204.e.push_back(e199);
				rt204.e.push_back(e1);
				rt204.e.push_back(e2);
				rt204.e.push_back(e151);
				rt204.e.push_back(e3);
				rt204.calc_arity(nullptr);
				raw_term rt207;
				rt207.neg = false;
				rt207.extype = raw_term::REL;
				rt207.e.push_back(e150);
				rt207.e.push_back(e1);
				rt207.e.push_back(e2);
				rt207.e.push_back(e151);
				rt207.e.push_back(e172);
				rt207.e.push_back(e3);
				rt207.calc_arity(nullptr);
				sprawformtree ft206 = std::make_shared<raw_form_tree>(elem::NONE, rt207);
				raw_term rt209;
				rt209.neg = false;
				rt209.extype = raw_term::REL;
				rt209.e.push_back(e199);
				rt209.e.push_back(e1);
				rt209.e.push_back(e172);
				rt209.e.push_back(e3);
				rt209.calc_arity(nullptr);
				sprawformtree ft208 = std::make_shared<raw_form_tree>(elem::NONE, rt209);
				sprawformtree ft205 = std::make_shared<raw_form_tree>(elem::AND, ft206, ft208);
				raw_rule rr210;
				rr210.h.push_back(rt204);
				rr210.set_prft(ft205);
				raw_term rt211;
				rt211.neg = false;
				rt211.extype = raw_term::REL;
				rt211.e.push_back(e199);
				rt211.e.push_back(e1);
				rt211.e.push_back(e2);
				rt211.e.push_back(e151);
				rt211.e.push_back(e39);
				rt211.e.push_back(e3);
				rt211.calc_arity(nullptr);
				raw_term rt214;
				rt214.neg = false;
				rt214.extype = raw_term::REL;
				rt214.e.push_back(e150);
				rt214.e.push_back(e1);
				rt214.e.push_back(e2);
				rt214.e.push_back(e151);
				rt214.e.push_back(e172);
				rt214.e.push_back(e3);
				rt214.calc_arity(nullptr);
				sprawformtree ft213 = std::make_shared<raw_form_tree>(elem::NONE, rt214);
				raw_term rt216;
				rt216.neg = false;
				rt216.extype = raw_term::REL;
				rt216.e.push_back(e199);
				rt216.e.push_back(e1);
				rt216.e.push_back(e172);
				rt216.e.push_back(e39);
				rt216.e.push_back(e3);
				rt216.calc_arity(nullptr);
				sprawformtree ft215 = std::make_shared<raw_form_tree>(elem::NONE, rt216);
				sprawformtree ft212 = std::make_shared<raw_form_tree>(elem::AND, ft213, ft215);
				raw_rule rr217;
				rr217.h.push_back(rt211);
				rr217.set_prft(ft212);
				raw_term rt218;
				rt218.neg = false;
				rt218.extype = raw_term::REL;
				rt218.e.push_back(e199);
				rt218.e.push_back(e1);
				rt218.e.push_back(e2);
				rt218.e.push_back(e151);
				rt218.e.push_back(e39);
				rt218.e.push_back(e152);
				rt218.e.push_back(e3);
				rt218.calc_arity(nullptr);
				raw_term rt221;
				rt221.neg = false;
				rt221.extype = raw_term::REL;
				rt221.e.push_back(e150);
				rt221.e.push_back(e1);
				rt221.e.push_back(e2);
				rt221.e.push_back(e151);
				rt221.e.push_back(e172);
				rt221.e.push_back(e3);
				rt221.calc_arity(nullptr);
				sprawformtree ft220 = std::make_shared<raw_form_tree>(elem::NONE, rt221);
				raw_term rt223;
				rt223.neg = false;
				rt223.extype = raw_term::REL;
				rt223.e.push_back(e199);
				rt223.e.push_back(e1);
				rt223.e.push_back(e172);
				rt223.e.push_back(e39);
				rt223.e.push_back(e152);
				rt223.e.push_back(e3);
				rt223.calc_arity(nullptr);
				sprawformtree ft222 = std::make_shared<raw_form_tree>(elem::NONE, rt223);
				sprawformtree ft219 = std::make_shared<raw_form_tree>(elem::AND, ft220, ft222);
				raw_rule rr224;
				rr224.h.push_back(rt218);
				rr224.set_prft(ft219);
				raw_term rt225;
				rt225.neg = false;
				rt225.extype = raw_term::REL;
				rt225.e.push_back(e199);
				rt225.e.push_back(e1);
				rt225.e.push_back(e2);
				rt225.e.push_back(e151);
				rt225.e.push_back(e39);
				rt225.e.push_back(e152);
				rt225.e.push_back(e191);
				rt225.e.push_back(e3);
				rt225.calc_arity(nullptr);
				raw_term rt228;
				rt228.neg = false;
				rt228.extype = raw_term::REL;
				rt228.e.push_back(e150);
				rt228.e.push_back(e1);
				rt228.e.push_back(e2);
				rt228.e.push_back(e151);
				rt228.e.push_back(e172);
				rt228.e.push_back(e3);
				rt228.calc_arity(nullptr);
				sprawformtree ft227 = std::make_shared<raw_form_tree>(elem::NONE, rt228);
				raw_term rt230;
				rt230.neg = false;
				rt230.extype = raw_term::REL;
				rt230.e.push_back(e199);
				rt230.e.push_back(e1);
				rt230.e.push_back(e172);
				rt230.e.push_back(e39);
				rt230.e.push_back(e152);
				rt230.e.push_back(e191);
				rt230.e.push_back(e3);
				rt230.calc_arity(nullptr);
				sprawformtree ft229 = std::make_shared<raw_form_tree>(elem::NONE, rt230);
				sprawformtree ft226 = std::make_shared<raw_form_tree>(elem::AND, ft227, ft229);
				raw_rule rr231;
				rr231.h.push_back(rt225);
				rr231.set_prft(ft226);
				elem e232;
				e232.type = elem::SYM;
				e232.e = d.get_lexeme("DO_RAPPEND0_CONS");
				elem e233;
				e233.type = elem::VAR;
				e233.e = d.get_lexeme("?xs");
				elem e234;
				e234.type = elem::VAR;
				e234.e = d.get_lexeme("?ys");
				raw_term rt235;
				rt235.neg = false;
				rt235.extype = raw_term::REL;
				rt235.e.push_back(e232);
				rt235.e.push_back(e1);
				rt235.e.push_back(e233);
				rt235.e.push_back(e234);
				rt235.e.push_back(e233);
				rt235.e.push_back(e234);
				rt235.e.push_back(e3);
				rt235.calc_arity(nullptr);
				elem e238;
				e238.type = elem::SYM;
				e238.e = d.get_lexeme("DO_RAPPEND_CONS");
				raw_term rt239;
				rt239.neg = false;
				rt239.extype = raw_term::REL;
				rt239.e.push_back(e238);
				rt239.e.push_back(e1);
				rt239.e.push_back(e233);
				rt239.e.push_back(e234);
				rt239.e.push_back(e3);
				rt239.calc_arity(nullptr);
				sprawformtree ft237 = std::make_shared<raw_form_tree>(elem::NONE, rt239);
				elem e243;
				e243.type = elem::VAR;
				e243.e = d.get_lexeme("?cs");
				sprawformtree ft242 = std::make_shared<raw_form_tree>(elem::VAR, e243);
				elem e245;
				e245.type = elem::SYM;
				e245.e = d.get_lexeme("RAPPEND_CONS");
				raw_term rt246;
				rt246.neg = false;
				rt246.extype = raw_term::REL;
				rt246.e.push_back(e245);
				rt246.e.push_back(e1);
				rt246.e.push_back(e243);
				rt246.e.push_back(e233);
				rt246.e.push_back(e234);
				rt246.e.push_back(e3);
				rt246.calc_arity(nullptr);
				sprawformtree ft244 = std::make_shared<raw_form_tree>(elem::NONE, rt246);
				sprawformtree ft241 = std::make_shared<raw_form_tree>(elem::EXISTS, ft242, ft244);
				sprawformtree ft240 = std::make_shared<raw_form_tree>(elem::NOT, ft241);
				sprawformtree ft236 = std::make_shared<raw_form_tree>(elem::AND, ft237, ft240);
				raw_rule rr247;
				rr247.h.push_back(rt235);
				rr247.set_prft(ft236);
				elem e248;
				e248.type = elem::VAR;
				e248.e = d.get_lexeme("?oxs");
				elem e249;
				e249.type = elem::VAR;
				e249.e = d.get_lexeme("?oys");
				elem e250;
				e250.type = elem::VAR;
				e250.e = d.get_lexeme("?xs_tl");
				raw_term rt251;
				rt251.neg = false;
				rt251.extype = raw_term::REL;
				rt251.e.push_back(e232);
				rt251.e.push_back(e1);
				rt251.e.push_back(e248);
				rt251.e.push_back(e249);
				rt251.e.push_back(e250);
				rt251.e.push_back(e234);
				rt251.e.push_back(e3);
				rt251.calc_arity(nullptr);
				elem e256;
				e256.type = elem::VAR;
				e256.e = d.get_lexeme("?ys_tl");
				raw_term rt257;
				rt257.neg = false;
				rt257.extype = raw_term::REL;
				rt257.e.push_back(e232);
				rt257.e.push_back(e1);
				rt257.e.push_back(e248);
				rt257.e.push_back(e249);
				rt257.e.push_back(e233);
				rt257.e.push_back(e256);
				rt257.e.push_back(e3);
				rt257.calc_arity(nullptr);
				sprawformtree ft255 = std::make_shared<raw_form_tree>(elem::NONE, rt257);
				elem e259;
				e259.type = elem::VAR;
				e259.e = d.get_lexeme("?xs_hd");
				raw_term rt260;
				rt260.neg = false;
				rt260.extype = raw_term::REL;
				rt260.e.push_back(e155);
				rt260.e.push_back(e1);
				rt260.e.push_back(e233);
				rt260.e.push_back(e259);
				rt260.e.push_back(e250);
				rt260.e.push_back(e3);
				rt260.calc_arity(nullptr);
				sprawformtree ft258 = std::make_shared<raw_form_tree>(elem::NONE, rt260);
				sprawformtree ft254 = std::make_shared<raw_form_tree>(elem::AND, ft255, ft258);
				raw_term rt262;
				rt262.neg = false;
				rt262.extype = raw_term::REL;
				rt262.e.push_back(e155);
				rt262.e.push_back(e1);
				rt262.e.push_back(e234);
				rt262.e.push_back(e259);
				rt262.e.push_back(e256);
				rt262.e.push_back(e3);
				rt262.calc_arity(nullptr);
				sprawformtree ft261 = std::make_shared<raw_form_tree>(elem::NONE, rt262);
				sprawformtree ft253 = std::make_shared<raw_form_tree>(elem::AND, ft254, ft261);
				sprawformtree ft265 = std::make_shared<raw_form_tree>(elem::VAR, e243);
				raw_term rt267;
				rt267.neg = false;
				rt267.extype = raw_term::REL;
				rt267.e.push_back(e245);
				rt267.e.push_back(e1);
				rt267.e.push_back(e243);
				rt267.e.push_back(e248);
				rt267.e.push_back(e249);
				rt267.e.push_back(e3);
				rt267.calc_arity(nullptr);
				sprawformtree ft266 = std::make_shared<raw_form_tree>(elem::NONE, rt267);
				sprawformtree ft264 = std::make_shared<raw_form_tree>(elem::EXISTS, ft265, ft266);
				sprawformtree ft263 = std::make_shared<raw_form_tree>(elem::NOT, ft264);
				sprawformtree ft252 = std::make_shared<raw_form_tree>(elem::AND, ft253, ft263);
				raw_rule rr268;
				rr268.h.push_back(rt251);
				rr268.set_prft(ft252);
				elem e269;
				e269.type = elem::VAR;
				e269.e = d.get_lexeme("?zs");
				raw_term rt270;
				rt270.neg = false;
				rt270.extype = raw_term::REL;
				rt270.e.push_back(e245);
				rt270.e.push_back(e1);
				rt270.e.push_back(e269);
				rt270.e.push_back(e233);
				rt270.e.push_back(e234);
				rt270.e.push_back(e3);
				rt270.calc_arity(nullptr);
				elem e274;
				e274.type = elem::VAR;
				e274.e = d.get_lexeme("?as");
				raw_term rt275;
				rt275.neg = false;
				rt275.extype = raw_term::REL;
				rt275.e.push_back(e232);
				rt275.e.push_back(e1);
				rt275.e.push_back(e233);
				rt275.e.push_back(e234);
				rt275.e.push_back(e274);
				rt275.e.push_back(e269);
				rt275.e.push_back(e3);
				rt275.calc_arity(nullptr);
				sprawformtree ft273 = std::make_shared<raw_form_tree>(elem::NONE, rt275);
				raw_term rt277;
				rt277.neg = false;
				rt277.extype = raw_term::REL;
				rt277.e.push_back(e155);
				rt277.e.push_back(e1);
				rt277.e.push_back(e274);
				rt277.e.push_back(e3);
				rt277.calc_arity(nullptr);
				sprawformtree ft276 = std::make_shared<raw_form_tree>(elem::NONE, rt277);
				sprawformtree ft272 = std::make_shared<raw_form_tree>(elem::AND, ft273, ft276);
				sprawformtree ft280 = std::make_shared<raw_form_tree>(elem::VAR, e243);
				raw_term rt282;
				rt282.neg = false;
				rt282.extype = raw_term::REL;
				rt282.e.push_back(e245);
				rt282.e.push_back(e1);
				rt282.e.push_back(e243);
				rt282.e.push_back(e233);
				rt282.e.push_back(e234);
				rt282.e.push_back(e3);
				rt282.calc_arity(nullptr);
				sprawformtree ft281 = std::make_shared<raw_form_tree>(elem::NONE, rt282);
				sprawformtree ft279 = std::make_shared<raw_form_tree>(elem::EXISTS, ft280, ft281);
				sprawformtree ft278 = std::make_shared<raw_form_tree>(elem::NOT, ft279);
				sprawformtree ft271 = std::make_shared<raw_form_tree>(elem::AND, ft272, ft278);
				raw_rule rr283;
				rr283.h.push_back(rt270);
				rr283.set_prft(ft271);
				raw_term rt284;
				rt284.neg = true;
				rt284.extype = raw_term::REL;
				rt284.e.push_back(e232);
				rt284.e.push_back(e1);
				rt284.e.push_back(e248);
				rt284.e.push_back(e249);
				rt284.e.push_back(e233);
				rt284.e.push_back(e234);
				rt284.e.push_back(e3);
				rt284.calc_arity(nullptr);
				raw_term rt286;
				rt286.neg = false;
				rt286.extype = raw_term::REL;
				rt286.e.push_back(e245);
				rt286.e.push_back(e1);
				rt286.e.push_back(e243);
				rt286.e.push_back(e248);
				rt286.e.push_back(e249);
				rt286.e.push_back(e3);
				rt286.calc_arity(nullptr);
				sprawformtree ft285 = std::make_shared<raw_form_tree>(elem::NONE, rt286);
				raw_rule rr287;
				rr287.h.push_back(rt284);
				rr287.set_prft(ft285);
				elem e288;
				e288.type = elem::SYM;
				e288.e = d.get_lexeme("DO_RAPPEND0_LST");
				raw_term rt289;
				rt289.neg = false;
				rt289.extype = raw_term::REL;
				rt289.e.push_back(e288);
				rt289.e.push_back(e1);
				rt289.e.push_back(e233);
				rt289.e.push_back(e234);
				rt289.e.push_back(e233);
				rt289.e.push_back(e234);
				rt289.e.push_back(e3);
				rt289.calc_arity(nullptr);
				elem e292;
				e292.type = elem::SYM;
				e292.e = d.get_lexeme("DO_RAPPEND_LST");
				raw_term rt293;
				rt293.neg = false;
				rt293.extype = raw_term::REL;
				rt293.e.push_back(e292);
				rt293.e.push_back(e1);
				rt293.e.push_back(e233);
				rt293.e.push_back(e234);
				rt293.e.push_back(e3);
				rt293.calc_arity(nullptr);
				sprawformtree ft291 = std::make_shared<raw_form_tree>(elem::NONE, rt293);
				sprawformtree ft296 = std::make_shared<raw_form_tree>(elem::VAR, e243);
				elem e298;
				e298.type = elem::SYM;
				e298.e = d.get_lexeme("RAPPEND_LST");
				raw_term rt299;
				rt299.neg = false;
				rt299.extype = raw_term::REL;
				rt299.e.push_back(e298);
				rt299.e.push_back(e1);
				rt299.e.push_back(e243);
				rt299.e.push_back(e233);
				rt299.e.push_back(e234);
				rt299.e.push_back(e3);
				rt299.calc_arity(nullptr);
				sprawformtree ft297 = std::make_shared<raw_form_tree>(elem::NONE, rt299);
				sprawformtree ft295 = std::make_shared<raw_form_tree>(elem::EXISTS, ft296, ft297);
				sprawformtree ft294 = std::make_shared<raw_form_tree>(elem::NOT, ft295);
				sprawformtree ft290 = std::make_shared<raw_form_tree>(elem::AND, ft291, ft294);
				raw_rule rr300;
				rr300.h.push_back(rt289);
				rr300.set_prft(ft290);
				raw_term rt301;
				rt301.neg = false;
				rt301.extype = raw_term::REL;
				rt301.e.push_back(e288);
				rt301.e.push_back(e1);
				rt301.e.push_back(e248);
				rt301.e.push_back(e249);
				rt301.e.push_back(e250);
				rt301.e.push_back(e234);
				rt301.e.push_back(e3);
				rt301.calc_arity(nullptr);
				raw_term rt306;
				rt306.neg = false;
				rt306.extype = raw_term::REL;
				rt306.e.push_back(e288);
				rt306.e.push_back(e1);
				rt306.e.push_back(e248);
				rt306.e.push_back(e249);
				rt306.e.push_back(e233);
				rt306.e.push_back(e256);
				rt306.e.push_back(e3);
				rt306.calc_arity(nullptr);
				sprawformtree ft305 = std::make_shared<raw_form_tree>(elem::NONE, rt306);
				raw_term rt308;
				rt308.neg = false;
				rt308.extype = raw_term::REL;
				rt308.e.push_back(e150);
				rt308.e.push_back(e1);
				rt308.e.push_back(e233);
				rt308.e.push_back(e259);
				rt308.e.push_back(e250);
				rt308.e.push_back(e3);
				rt308.calc_arity(nullptr);
				sprawformtree ft307 = std::make_shared<raw_form_tree>(elem::NONE, rt308);
				sprawformtree ft304 = std::make_shared<raw_form_tree>(elem::AND, ft305, ft307);
				raw_term rt310;
				rt310.neg = false;
				rt310.extype = raw_term::REL;
				rt310.e.push_back(e150);
				rt310.e.push_back(e1);
				rt310.e.push_back(e234);
				rt310.e.push_back(e259);
				rt310.e.push_back(e256);
				rt310.e.push_back(e3);
				rt310.calc_arity(nullptr);
				sprawformtree ft309 = std::make_shared<raw_form_tree>(elem::NONE, rt310);
				sprawformtree ft303 = std::make_shared<raw_form_tree>(elem::AND, ft304, ft309);
				sprawformtree ft313 = std::make_shared<raw_form_tree>(elem::VAR, e243);
				raw_term rt315;
				rt315.neg = false;
				rt315.extype = raw_term::REL;
				rt315.e.push_back(e298);
				rt315.e.push_back(e1);
				rt315.e.push_back(e243);
				rt315.e.push_back(e248);
				rt315.e.push_back(e249);
				rt315.e.push_back(e3);
				rt315.calc_arity(nullptr);
				sprawformtree ft314 = std::make_shared<raw_form_tree>(elem::NONE, rt315);
				sprawformtree ft312 = std::make_shared<raw_form_tree>(elem::EXISTS, ft313, ft314);
				sprawformtree ft311 = std::make_shared<raw_form_tree>(elem::NOT, ft312);
				sprawformtree ft302 = std::make_shared<raw_form_tree>(elem::AND, ft303, ft311);
				raw_rule rr316;
				rr316.h.push_back(rt301);
				rr316.set_prft(ft302);
				raw_term rt317;
				rt317.neg = false;
				rt317.extype = raw_term::REL;
				rt317.e.push_back(e298);
				rt317.e.push_back(e1);
				rt317.e.push_back(e269);
				rt317.e.push_back(e233);
				rt317.e.push_back(e234);
				rt317.e.push_back(e3);
				rt317.calc_arity(nullptr);
				raw_term rt321;
				rt321.neg = false;
				rt321.extype = raw_term::REL;
				rt321.e.push_back(e288);
				rt321.e.push_back(e1);
				rt321.e.push_back(e233);
				rt321.e.push_back(e234);
				rt321.e.push_back(e274);
				rt321.e.push_back(e269);
				rt321.e.push_back(e3);
				rt321.calc_arity(nullptr);
				sprawformtree ft320 = std::make_shared<raw_form_tree>(elem::NONE, rt321);
				raw_term rt323;
				rt323.neg = false;
				rt323.extype = raw_term::REL;
				rt323.e.push_back(e150);
				rt323.e.push_back(e1);
				rt323.e.push_back(e274);
				rt323.e.push_back(e3);
				rt323.calc_arity(nullptr);
				sprawformtree ft322 = std::make_shared<raw_form_tree>(elem::NONE, rt323);
				sprawformtree ft319 = std::make_shared<raw_form_tree>(elem::AND, ft320, ft322);
				sprawformtree ft326 = std::make_shared<raw_form_tree>(elem::VAR, e243);
				raw_term rt328;
				rt328.neg = false;
				rt328.extype = raw_term::REL;
				rt328.e.push_back(e298);
				rt328.e.push_back(e1);
				rt328.e.push_back(e243);
				rt328.e.push_back(e233);
				rt328.e.push_back(e234);
				rt328.e.push_back(e3);
				rt328.calc_arity(nullptr);
				sprawformtree ft327 = std::make_shared<raw_form_tree>(elem::NONE, rt328);
				sprawformtree ft325 = std::make_shared<raw_form_tree>(elem::EXISTS, ft326, ft327);
				sprawformtree ft324 = std::make_shared<raw_form_tree>(elem::NOT, ft325);
				sprawformtree ft318 = std::make_shared<raw_form_tree>(elem::AND, ft319, ft324);
				raw_rule rr329;
				rr329.h.push_back(rt317);
				rr329.set_prft(ft318);
				raw_term rt330;
				rt330.neg = true;
				rt330.extype = raw_term::REL;
				rt330.e.push_back(e288);
				rt330.e.push_back(e1);
				rt330.e.push_back(e248);
				rt330.e.push_back(e249);
				rt330.e.push_back(e233);
				rt330.e.push_back(e234);
				rt330.e.push_back(e3);
				rt330.calc_arity(nullptr);
				raw_term rt332;
				rt332.neg = false;
				rt332.extype = raw_term::REL;
				rt332.e.push_back(e298);
				rt332.e.push_back(e1);
				rt332.e.push_back(e243);
				rt332.e.push_back(e248);
				rt332.e.push_back(e249);
				rt332.e.push_back(e3);
				rt332.calc_arity(nullptr);
				sprawformtree ft331 = std::make_shared<raw_form_tree>(elem::NONE, rt332);
				raw_rule rr333;
				rr333.h.push_back(rt330);
				rr333.set_prft(ft331);
				elem e334;
				e334.type = elem::SYM;
				e334.e = d.get_lexeme("DO_REVERSE_CONS");
				elem e335;
				e335.type = elem::VAR;
				e335.e = d.get_lexeme("?bs");
				raw_term rt336;
				rt336.neg = false;
				rt336.extype = raw_term::REL;
				rt336.e.push_back(e334);
				rt336.e.push_back(e1);
				rt336.e.push_back(e335);
				rt336.e.push_back(e274);
				rt336.e.push_back(e335);
				rt336.e.push_back(e3);
				rt336.calc_arity(nullptr);
				raw_term rt340;
				rt340.neg = false;
				rt340.extype = raw_term::REL;
				rt340.e.push_back(e334);
				rt340.e.push_back(e1);
				rt340.e.push_back(e335);
				rt340.e.push_back(e3);
				rt340.calc_arity(nullptr);
				sprawformtree ft339 = std::make_shared<raw_form_tree>(elem::NONE, rt340);
				raw_term rt342;
				rt342.neg = false;
				rt342.extype = raw_term::REL;
				rt342.e.push_back(e155);
				rt342.e.push_back(e1);
				rt342.e.push_back(e274);
				rt342.e.push_back(e3);
				rt342.calc_arity(nullptr);
				sprawformtree ft341 = std::make_shared<raw_form_tree>(elem::NONE, rt342);
				sprawformtree ft338 = std::make_shared<raw_form_tree>(elem::AND, ft339, ft341);
				sprawformtree ft345 = std::make_shared<raw_form_tree>(elem::VAR, e151);
				elem e347;
				e347.type = elem::SYM;
				e347.e = d.get_lexeme("REVERSE_CONS");
				raw_term rt348;
				rt348.neg = false;
				rt348.extype = raw_term::REL;
				rt348.e.push_back(e347);
				rt348.e.push_back(e1);
				rt348.e.push_back(e335);
				rt348.e.push_back(e151);
				rt348.e.push_back(e3);
				rt348.calc_arity(nullptr);
				sprawformtree ft346 = std::make_shared<raw_form_tree>(elem::NONE, rt348);
				sprawformtree ft344 = std::make_shared<raw_form_tree>(elem::EXISTS, ft345, ft346);
				sprawformtree ft343 = std::make_shared<raw_form_tree>(elem::NOT, ft344);
				sprawformtree ft337 = std::make_shared<raw_form_tree>(elem::AND, ft338, ft343);
				raw_rule rr349;
				rr349.h.push_back(rt336);
				rr349.set_prft(ft337);
				elem e350;
				e350.type = elem::VAR;
				e350.e = d.get_lexeme("?obs");
				raw_term rt351;
				rt351.neg = false;
				rt351.extype = raw_term::REL;
				rt351.e.push_back(e334);
				rt351.e.push_back(e1);
				rt351.e.push_back(e350);
				rt351.e.push_back(e274);
				rt351.e.push_back(e335);
				rt351.e.push_back(e3);
				rt351.calc_arity(nullptr);
				elem e356;
				e356.type = elem::VAR;
				e356.e = d.get_lexeme("?as_hd");
				elem e357;
				e357.type = elem::VAR;
				e357.e = d.get_lexeme("?as_tl");
				raw_term rt358;
				rt358.neg = false;
				rt358.extype = raw_term::REL;
				rt358.e.push_back(e155);
				rt358.e.push_back(e1);
				rt358.e.push_back(e274);
				rt358.e.push_back(e356);
				rt358.e.push_back(e357);
				rt358.e.push_back(e3);
				rt358.calc_arity(nullptr);
				sprawformtree ft355 = std::make_shared<raw_form_tree>(elem::NONE, rt358);
				elem e360;
				e360.type = elem::VAR;
				e360.e = d.get_lexeme("?nbs");
				raw_term rt361;
				rt361.neg = false;
				rt361.extype = raw_term::REL;
				rt361.e.push_back(e155);
				rt361.e.push_back(e1);
				rt361.e.push_back(e360);
				rt361.e.push_back(e356);
				rt361.e.push_back(e335);
				rt361.e.push_back(e3);
				rt361.calc_arity(nullptr);
				sprawformtree ft359 = std::make_shared<raw_form_tree>(elem::NONE, rt361);
				sprawformtree ft354 = std::make_shared<raw_form_tree>(elem::AND, ft355, ft359);
				raw_term rt363;
				rt363.neg = false;
				rt363.extype = raw_term::REL;
				rt363.e.push_back(e334);
				rt363.e.push_back(e1);
				rt363.e.push_back(e350);
				rt363.e.push_back(e357);
				rt363.e.push_back(e360);
				rt363.e.push_back(e3);
				rt363.calc_arity(nullptr);
				sprawformtree ft362 = std::make_shared<raw_form_tree>(elem::NONE, rt363);
				sprawformtree ft353 = std::make_shared<raw_form_tree>(elem::AND, ft354, ft362);
				sprawformtree ft366 = std::make_shared<raw_form_tree>(elem::VAR, e151);
				raw_term rt368;
				rt368.neg = false;
				rt368.extype = raw_term::REL;
				rt368.e.push_back(e347);
				rt368.e.push_back(e1);
				rt368.e.push_back(e350);
				rt368.e.push_back(e151);
				rt368.e.push_back(e3);
				rt368.calc_arity(nullptr);
				sprawformtree ft367 = std::make_shared<raw_form_tree>(elem::NONE, rt368);
				sprawformtree ft365 = std::make_shared<raw_form_tree>(elem::EXISTS, ft366, ft367);
				sprawformtree ft364 = std::make_shared<raw_form_tree>(elem::NOT, ft365);
				sprawformtree ft352 = std::make_shared<raw_form_tree>(elem::AND, ft353, ft364);
				raw_rule rr369;
				rr369.h.push_back(rt351);
				rr369.set_prft(ft352);
				raw_term rt370;
				rt370.neg = false;
				rt370.extype = raw_term::REL;
				rt370.e.push_back(e347);
				rt370.e.push_back(e1);
				rt370.e.push_back(e350);
				rt370.e.push_back(e274);
				rt370.e.push_back(e3);
				rt370.calc_arity(nullptr);
				raw_term rt374;
				rt374.neg = false;
				rt374.extype = raw_term::REL;
				rt374.e.push_back(e334);
				rt374.e.push_back(e1);
				rt374.e.push_back(e350);
				rt374.e.push_back(e274);
				rt374.e.push_back(e335);
				rt374.e.push_back(e3);
				rt374.calc_arity(nullptr);
				sprawformtree ft373 = std::make_shared<raw_form_tree>(elem::NONE, rt374);
				raw_term rt376;
				rt376.neg = false;
				rt376.extype = raw_term::REL;
				rt376.e.push_back(e155);
				rt376.e.push_back(e1);
				rt376.e.push_back(e335);
				rt376.e.push_back(e3);
				rt376.calc_arity(nullptr);
				sprawformtree ft375 = std::make_shared<raw_form_tree>(elem::NONE, rt376);
				sprawformtree ft372 = std::make_shared<raw_form_tree>(elem::AND, ft373, ft375);
				sprawformtree ft379 = std::make_shared<raw_form_tree>(elem::VAR, e151);
				raw_term rt381;
				rt381.neg = false;
				rt381.extype = raw_term::REL;
				rt381.e.push_back(e347);
				rt381.e.push_back(e1);
				rt381.e.push_back(e350);
				rt381.e.push_back(e151);
				rt381.e.push_back(e3);
				rt381.calc_arity(nullptr);
				sprawformtree ft380 = std::make_shared<raw_form_tree>(elem::NONE, rt381);
				sprawformtree ft378 = std::make_shared<raw_form_tree>(elem::EXISTS, ft379, ft380);
				sprawformtree ft377 = std::make_shared<raw_form_tree>(elem::NOT, ft378);
				sprawformtree ft371 = std::make_shared<raw_form_tree>(elem::AND, ft372, ft377);
				raw_rule rr382;
				rr382.h.push_back(rt370);
				rr382.set_prft(ft371);
				raw_term rt383;
				rt383.neg = true;
				rt383.extype = raw_term::REL;
				rt383.e.push_back(e334);
				rt383.e.push_back(e1);
				rt383.e.push_back(e350);
				rt383.e.push_back(e274);
				rt383.e.push_back(e335);
				rt383.e.push_back(e3);
				rt383.calc_arity(nullptr);
				raw_term rt385;
				rt385.neg = false;
				rt385.extype = raw_term::REL;
				rt385.e.push_back(e347);
				rt385.e.push_back(e1);
				rt385.e.push_back(e350);
				rt385.e.push_back(e243);
				rt385.e.push_back(e3);
				rt385.calc_arity(nullptr);
				sprawformtree ft384 = std::make_shared<raw_form_tree>(elem::NONE, rt385);
				raw_rule rr386;
				rr386.h.push_back(rt383);
				rr386.set_prft(ft384);
				elem e387;
				e387.type = elem::SYM;
				e387.e = d.get_lexeme("DO_REVERSE_LST");
				raw_term rt388;
				rt388.neg = false;
				rt388.extype = raw_term::REL;
				rt388.e.push_back(e387);
				rt388.e.push_back(e1);
				rt388.e.push_back(e335);
				rt388.e.push_back(e274);
				rt388.e.push_back(e335);
				rt388.e.push_back(e3);
				rt388.calc_arity(nullptr);
				raw_term rt392;
				rt392.neg = false;
				rt392.extype = raw_term::REL;
				rt392.e.push_back(e387);
				rt392.e.push_back(e1);
				rt392.e.push_back(e335);
				rt392.e.push_back(e3);
				rt392.calc_arity(nullptr);
				sprawformtree ft391 = std::make_shared<raw_form_tree>(elem::NONE, rt392);
				raw_term rt394;
				rt394.neg = false;
				rt394.extype = raw_term::REL;
				rt394.e.push_back(e150);
				rt394.e.push_back(e1);
				rt394.e.push_back(e274);
				rt394.e.push_back(e3);
				rt394.calc_arity(nullptr);
				sprawformtree ft393 = std::make_shared<raw_form_tree>(elem::NONE, rt394);
				sprawformtree ft390 = std::make_shared<raw_form_tree>(elem::AND, ft391, ft393);
				sprawformtree ft397 = std::make_shared<raw_form_tree>(elem::VAR, e151);
				elem e399;
				e399.type = elem::SYM;
				e399.e = d.get_lexeme("REVERSE_LST");
				raw_term rt400;
				rt400.neg = false;
				rt400.extype = raw_term::REL;
				rt400.e.push_back(e399);
				rt400.e.push_back(e1);
				rt400.e.push_back(e335);
				rt400.e.push_back(e151);
				rt400.e.push_back(e3);
				rt400.calc_arity(nullptr);
				sprawformtree ft398 = std::make_shared<raw_form_tree>(elem::NONE, rt400);
				sprawformtree ft396 = std::make_shared<raw_form_tree>(elem::EXISTS, ft397, ft398);
				sprawformtree ft395 = std::make_shared<raw_form_tree>(elem::NOT, ft396);
				sprawformtree ft389 = std::make_shared<raw_form_tree>(elem::AND, ft390, ft395);
				raw_rule rr401;
				rr401.h.push_back(rt388);
				rr401.set_prft(ft389);
				raw_term rt402;
				rt402.neg = false;
				rt402.extype = raw_term::REL;
				rt402.e.push_back(e387);
				rt402.e.push_back(e1);
				rt402.e.push_back(e350);
				rt402.e.push_back(e274);
				rt402.e.push_back(e335);
				rt402.e.push_back(e3);
				rt402.calc_arity(nullptr);
				raw_term rt407;
				rt407.neg = false;
				rt407.extype = raw_term::REL;
				rt407.e.push_back(e150);
				rt407.e.push_back(e1);
				rt407.e.push_back(e274);
				rt407.e.push_back(e356);
				rt407.e.push_back(e357);
				rt407.e.push_back(e3);
				rt407.calc_arity(nullptr);
				sprawformtree ft406 = std::make_shared<raw_form_tree>(elem::NONE, rt407);
				raw_term rt409;
				rt409.neg = false;
				rt409.extype = raw_term::REL;
				rt409.e.push_back(e150);
				rt409.e.push_back(e1);
				rt409.e.push_back(e360);
				rt409.e.push_back(e356);
				rt409.e.push_back(e335);
				rt409.e.push_back(e3);
				rt409.calc_arity(nullptr);
				sprawformtree ft408 = std::make_shared<raw_form_tree>(elem::NONE, rt409);
				sprawformtree ft405 = std::make_shared<raw_form_tree>(elem::AND, ft406, ft408);
				raw_term rt411;
				rt411.neg = false;
				rt411.extype = raw_term::REL;
				rt411.e.push_back(e387);
				rt411.e.push_back(e1);
				rt411.e.push_back(e350);
				rt411.e.push_back(e357);
				rt411.e.push_back(e360);
				rt411.e.push_back(e3);
				rt411.calc_arity(nullptr);
				sprawformtree ft410 = std::make_shared<raw_form_tree>(elem::NONE, rt411);
				sprawformtree ft404 = std::make_shared<raw_form_tree>(elem::AND, ft405, ft410);
				sprawformtree ft414 = std::make_shared<raw_form_tree>(elem::VAR, e151);
				raw_term rt416;
				rt416.neg = false;
				rt416.extype = raw_term::REL;
				rt416.e.push_back(e399);
				rt416.e.push_back(e1);
				rt416.e.push_back(e350);
				rt416.e.push_back(e151);
				rt416.e.push_back(e3);
				rt416.calc_arity(nullptr);
				sprawformtree ft415 = std::make_shared<raw_form_tree>(elem::NONE, rt416);
				sprawformtree ft413 = std::make_shared<raw_form_tree>(elem::EXISTS, ft414, ft415);
				sprawformtree ft412 = std::make_shared<raw_form_tree>(elem::NOT, ft413);
				sprawformtree ft403 = std::make_shared<raw_form_tree>(elem::AND, ft404, ft412);
				raw_rule rr417;
				rr417.h.push_back(rt402);
				rr417.set_prft(ft403);
				raw_term rt418;
				rt418.neg = false;
				rt418.extype = raw_term::REL;
				rt418.e.push_back(e399);
				rt418.e.push_back(e1);
				rt418.e.push_back(e350);
				rt418.e.push_back(e274);
				rt418.e.push_back(e3);
				rt418.calc_arity(nullptr);
				raw_term rt422;
				rt422.neg = false;
				rt422.extype = raw_term::REL;
				rt422.e.push_back(e387);
				rt422.e.push_back(e1);
				rt422.e.push_back(e350);
				rt422.e.push_back(e274);
				rt422.e.push_back(e335);
				rt422.e.push_back(e3);
				rt422.calc_arity(nullptr);
				sprawformtree ft421 = std::make_shared<raw_form_tree>(elem::NONE, rt422);
				raw_term rt424;
				rt424.neg = false;
				rt424.extype = raw_term::REL;
				rt424.e.push_back(e150);
				rt424.e.push_back(e1);
				rt424.e.push_back(e335);
				rt424.e.push_back(e3);
				rt424.calc_arity(nullptr);
				sprawformtree ft423 = std::make_shared<raw_form_tree>(elem::NONE, rt424);
				sprawformtree ft420 = std::make_shared<raw_form_tree>(elem::AND, ft421, ft423);
				sprawformtree ft427 = std::make_shared<raw_form_tree>(elem::VAR, e151);
				raw_term rt429;
				rt429.neg = false;
				rt429.extype = raw_term::REL;
				rt429.e.push_back(e399);
				rt429.e.push_back(e1);
				rt429.e.push_back(e350);
				rt429.e.push_back(e151);
				rt429.e.push_back(e3);
				rt429.calc_arity(nullptr);
				sprawformtree ft428 = std::make_shared<raw_form_tree>(elem::NONE, rt429);
				sprawformtree ft426 = std::make_shared<raw_form_tree>(elem::EXISTS, ft427, ft428);
				sprawformtree ft425 = std::make_shared<raw_form_tree>(elem::NOT, ft426);
				sprawformtree ft419 = std::make_shared<raw_form_tree>(elem::AND, ft420, ft425);
				raw_rule rr430;
				rr430.h.push_back(rt418);
				rr430.set_prft(ft419);
				raw_term rt431;
				rt431.neg = true;
				rt431.extype = raw_term::REL;
				rt431.e.push_back(e387);
				rt431.e.push_back(e1);
				rt431.e.push_back(e350);
				rt431.e.push_back(e274);
				rt431.e.push_back(e335);
				rt431.e.push_back(e3);
				rt431.calc_arity(nullptr);
				raw_term rt433;
				rt433.neg = false;
				rt433.extype = raw_term::REL;
				rt433.e.push_back(e399);
				rt433.e.push_back(e1);
				rt433.e.push_back(e350);
				rt433.e.push_back(e243);
				rt433.e.push_back(e3);
				rt433.calc_arity(nullptr);
				sprawformtree ft432 = std::make_shared<raw_form_tree>(elem::NONE, rt433);
				raw_rule rr434;
				rr434.h.push_back(rt431);
				rr434.set_prft(ft432);
				elem e435;
				e435.type = elem::SYM;
				e435.e = d.get_lexeme("ASSOC0");
				raw_term rt436;
				rt436.neg = false;
				rt436.extype = raw_term::REL;
				rt436.e.push_back(e435);
				rt436.e.push_back(e1);
				rt436.e.push_back(e233);
				rt436.e.push_back(e234);
				rt436.e.push_back(e233);
				rt436.e.push_back(e234);
				rt436.e.push_back(e59);
				rt436.e.push_back(e3);
				rt436.calc_arity(nullptr);
				elem e440;
				e440.type = elem::SYM;
				e440.e = d.get_lexeme("ASSOC");
				raw_term rt441;
				rt441.neg = false;
				rt441.extype = raw_term::REL;
				rt441.e.push_back(e440);
				rt441.e.push_back(e1);
				rt441.e.push_back(e233);
				rt441.e.push_back(e234);
				rt441.e.push_back(e59);
				rt441.e.push_back(e3);
				rt441.calc_arity(nullptr);
				sprawformtree ft439 = std::make_shared<raw_form_tree>(elem::NONE, rt441);
				sprawformtree ft444 = std::make_shared<raw_form_tree>(elem::VAR, e47);
				raw_term rt446;
				rt446.neg = false;
				rt446.extype = raw_term::REL;
				rt446.e.push_back(e440);
				rt446.e.push_back(e1);
				rt446.e.push_back(e233);
				rt446.e.push_back(e234);
				rt446.e.push_back(e59);
				rt446.e.push_back(e47);
				rt446.e.push_back(e3);
				rt446.calc_arity(nullptr);
				sprawformtree ft445 = std::make_shared<raw_form_tree>(elem::NONE, rt446);
				sprawformtree ft443 = std::make_shared<raw_form_tree>(elem::EXISTS, ft444, ft445);
				sprawformtree ft442 = std::make_shared<raw_form_tree>(elem::NOT, ft443);
				sprawformtree ft438 = std::make_shared<raw_form_tree>(elem::AND, ft439, ft442);
				elem e449;
				e449.type = elem::SYM;
				e449.e = d.get_lexeme("NO_ASSOC");
				raw_term rt450;
				rt450.neg = false;
				rt450.extype = raw_term::REL;
				rt450.e.push_back(e449);
				rt450.e.push_back(e1);
				rt450.e.push_back(e233);
				rt450.e.push_back(e234);
				rt450.e.push_back(e59);
				rt450.e.push_back(e3);
				rt450.calc_arity(nullptr);
				sprawformtree ft448 = std::make_shared<raw_form_tree>(elem::NONE, rt450);
				sprawformtree ft447 = std::make_shared<raw_form_tree>(elem::NOT, ft448);
				sprawformtree ft437 = std::make_shared<raw_form_tree>(elem::AND, ft438, ft447);
				raw_rule rr451;
				rr451.h.push_back(rt436);
				rr451.set_prft(ft437);
				elem e452;
				e452.type = elem::VAR;
				e452.e = d.get_lexeme("?yn");
				raw_term rt453;
				rt453.neg = false;
				rt453.extype = raw_term::REL;
				rt453.e.push_back(e435);
				rt453.e.push_back(e1);
				rt453.e.push_back(e248);
				rt453.e.push_back(e249);
				rt453.e.push_back(e250);
				rt453.e.push_back(e256);
				rt453.e.push_back(e59);
				rt453.e.push_back(e452);
				rt453.e.push_back(e3);
				rt453.calc_arity(nullptr);
				raw_term rt459;
				rt459.neg = false;
				rt459.extype = raw_term::REL;
				rt459.e.push_back(e155);
				rt459.e.push_back(e1);
				rt459.e.push_back(e233);
				rt459.e.push_back(e59);
				rt459.e.push_back(e250);
				rt459.e.push_back(e3);
				rt459.calc_arity(nullptr);
				sprawformtree ft458 = std::make_shared<raw_form_tree>(elem::NONE, rt459);
				raw_term rt461;
				rt461.neg = false;
				rt461.extype = raw_term::REL;
				rt461.e.push_back(e155);
				rt461.e.push_back(e1);
				rt461.e.push_back(e234);
				rt461.e.push_back(e452);
				rt461.e.push_back(e256);
				rt461.e.push_back(e3);
				rt461.calc_arity(nullptr);
				sprawformtree ft460 = std::make_shared<raw_form_tree>(elem::NONE, rt461);
				sprawformtree ft457 = std::make_shared<raw_form_tree>(elem::AND, ft458, ft460);
				raw_term rt463;
				rt463.neg = false;
				rt463.extype = raw_term::REL;
				rt463.e.push_back(e435);
				rt463.e.push_back(e1);
				rt463.e.push_back(e248);
				rt463.e.push_back(e249);
				rt463.e.push_back(e233);
				rt463.e.push_back(e234);
				rt463.e.push_back(e59);
				rt463.e.push_back(e3);
				rt463.calc_arity(nullptr);
				sprawformtree ft462 = std::make_shared<raw_form_tree>(elem::NONE, rt463);
				sprawformtree ft456 = std::make_shared<raw_form_tree>(elem::AND, ft457, ft462);
				sprawformtree ft466 = std::make_shared<raw_form_tree>(elem::VAR, e47);
				raw_term rt468;
				rt468.neg = false;
				rt468.extype = raw_term::REL;
				rt468.e.push_back(e440);
				rt468.e.push_back(e1);
				rt468.e.push_back(e248);
				rt468.e.push_back(e249);
				rt468.e.push_back(e59);
				rt468.e.push_back(e47);
				rt468.e.push_back(e3);
				rt468.calc_arity(nullptr);
				sprawformtree ft467 = std::make_shared<raw_form_tree>(elem::NONE, rt468);
				sprawformtree ft465 = std::make_shared<raw_form_tree>(elem::EXISTS, ft466, ft467);
				sprawformtree ft464 = std::make_shared<raw_form_tree>(elem::NOT, ft465);
				sprawformtree ft455 = std::make_shared<raw_form_tree>(elem::AND, ft456, ft464);
				raw_term rt471;
				rt471.neg = false;
				rt471.extype = raw_term::REL;
				rt471.e.push_back(e449);
				rt471.e.push_back(e1);
				rt471.e.push_back(e248);
				rt471.e.push_back(e249);
				rt471.e.push_back(e59);
				rt471.e.push_back(e3);
				rt471.calc_arity(nullptr);
				sprawformtree ft470 = std::make_shared<raw_form_tree>(elem::NONE, rt471);
				sprawformtree ft469 = std::make_shared<raw_form_tree>(elem::NOT, ft470);
				sprawformtree ft454 = std::make_shared<raw_form_tree>(elem::AND, ft455, ft469);
				raw_rule rr472;
				rr472.h.push_back(rt453);
				rr472.set_prft(ft454);
				raw_term rt473;
				rt473.neg = false;
				rt473.extype = raw_term::REL;
				rt473.e.push_back(e449);
				rt473.e.push_back(e1);
				rt473.e.push_back(e248);
				rt473.e.push_back(e249);
				rt473.e.push_back(e59);
				rt473.e.push_back(e3);
				rt473.calc_arity(nullptr);
				raw_term rt479;
				rt479.neg = false;
				rt479.extype = raw_term::REL;
				rt479.e.push_back(e155);
				rt479.e.push_back(e1);
				rt479.e.push_back(e233);
				rt479.e.push_back(e59);
				rt479.e.push_back(e250);
				rt479.e.push_back(e3);
				rt479.calc_arity(nullptr);
				sprawformtree ft478 = std::make_shared<raw_form_tree>(elem::NONE, rt479);
				raw_term rt481;
				rt481.neg = false;
				rt481.extype = raw_term::REL;
				rt481.e.push_back(e155);
				rt481.e.push_back(e1);
				rt481.e.push_back(e234);
				rt481.e.push_back(e452);
				rt481.e.push_back(e256);
				rt481.e.push_back(e3);
				rt481.calc_arity(nullptr);
				sprawformtree ft480 = std::make_shared<raw_form_tree>(elem::NONE, rt481);
				sprawformtree ft477 = std::make_shared<raw_form_tree>(elem::AND, ft478, ft480);
				raw_term rt483;
				rt483.neg = false;
				rt483.extype = raw_term::REL;
				rt483.e.push_back(e435);
				rt483.e.push_back(e1);
				rt483.e.push_back(e248);
				rt483.e.push_back(e249);
				rt483.e.push_back(e233);
				rt483.e.push_back(e234);
				rt483.e.push_back(e59);
				rt483.e.push_back(e47);
				rt483.e.push_back(e3);
				rt483.calc_arity(nullptr);
				sprawformtree ft482 = std::make_shared<raw_form_tree>(elem::NONE, rt483);
				sprawformtree ft476 = std::make_shared<raw_form_tree>(elem::AND, ft477, ft482);
				sprawformtree ft486 = std::make_shared<raw_form_tree>(elem::VAR, e47);
				raw_term rt488;
				rt488.neg = false;
				rt488.extype = raw_term::REL;
				rt488.e.push_back(e440);
				rt488.e.push_back(e1);
				rt488.e.push_back(e248);
				rt488.e.push_back(e249);
				rt488.e.push_back(e59);
				rt488.e.push_back(e47);
				rt488.e.push_back(e3);
				rt488.calc_arity(nullptr);
				sprawformtree ft487 = std::make_shared<raw_form_tree>(elem::NONE, rt488);
				sprawformtree ft485 = std::make_shared<raw_form_tree>(elem::EXISTS, ft486, ft487);
				sprawformtree ft484 = std::make_shared<raw_form_tree>(elem::NOT, ft485);
				sprawformtree ft475 = std::make_shared<raw_form_tree>(elem::AND, ft476, ft484);
				raw_term rt491;
				rt491.neg = false;
				rt491.extype = raw_term::REL;
				rt491.e.push_back(e449);
				rt491.e.push_back(e1);
				rt491.e.push_back(e248);
				rt491.e.push_back(e249);
				rt491.e.push_back(e59);
				rt491.e.push_back(e3);
				rt491.calc_arity(nullptr);
				sprawformtree ft490 = std::make_shared<raw_form_tree>(elem::NONE, rt491);
				sprawformtree ft489 = std::make_shared<raw_form_tree>(elem::NOT, ft490);
				sprawformtree ft474 = std::make_shared<raw_form_tree>(elem::AND, ft475, ft489);
				raw_rule rr492;
				rr492.h.push_back(rt473);
				rr492.set_prft(ft474);
				raw_term rt493;
				rt493.neg = false;
				rt493.extype = raw_term::REL;
				rt493.e.push_back(e435);
				rt493.e.push_back(e1);
				rt493.e.push_back(e248);
				rt493.e.push_back(e249);
				rt493.e.push_back(e250);
				rt493.e.push_back(e256);
				rt493.e.push_back(e59);
				rt493.e.push_back(e3);
				rt493.calc_arity(nullptr);
				elem e500;
				e500.type = elem::VAR;
				e500.e = d.get_lexeme("?xn");
				raw_term rt501;
				rt501.neg = false;
				rt501.extype = raw_term::REL;
				rt501.e.push_back(e155);
				rt501.e.push_back(e1);
				rt501.e.push_back(e233);
				rt501.e.push_back(e500);
				rt501.e.push_back(e250);
				rt501.e.push_back(e3);
				rt501.calc_arity(nullptr);
				sprawformtree ft499 = std::make_shared<raw_form_tree>(elem::NONE, rt501);
				raw_term rt503;
				rt503.neg = false;
				rt503.extype = raw_term::REL;
				rt503.e.push_back(e155);
				rt503.e.push_back(e1);
				rt503.e.push_back(e234);
				rt503.e.push_back(e452);
				rt503.e.push_back(e256);
				rt503.e.push_back(e3);
				rt503.calc_arity(nullptr);
				sprawformtree ft502 = std::make_shared<raw_form_tree>(elem::NONE, rt503);
				sprawformtree ft498 = std::make_shared<raw_form_tree>(elem::AND, ft499, ft502);
				raw_term rt505;
				rt505.neg = false;
				rt505.extype = raw_term::REL;
				rt505.e.push_back(e435);
				rt505.e.push_back(e1);
				rt505.e.push_back(e248);
				rt505.e.push_back(e249);
				rt505.e.push_back(e233);
				rt505.e.push_back(e234);
				rt505.e.push_back(e59);
				rt505.e.push_back(e3);
				rt505.calc_arity(nullptr);
				sprawformtree ft504 = std::make_shared<raw_form_tree>(elem::NONE, rt505);
				sprawformtree ft497 = std::make_shared<raw_form_tree>(elem::AND, ft498, ft504);
				raw_term rt508;
				rt508.neg = false;
				rt508.extype = raw_term::EQ;
				rt508.e.push_back(e500);
				rt508.e.push_back(e109);
				rt508.e.push_back(e59);
				rt508.calc_arity(nullptr);
				sprawformtree ft507 = std::make_shared<raw_form_tree>(elem::NONE, rt508);
				sprawformtree ft506 = std::make_shared<raw_form_tree>(elem::NOT, ft507);
				sprawformtree ft496 = std::make_shared<raw_form_tree>(elem::AND, ft497, ft506);
				sprawformtree ft511 = std::make_shared<raw_form_tree>(elem::VAR, e47);
				raw_term rt513;
				rt513.neg = false;
				rt513.extype = raw_term::REL;
				rt513.e.push_back(e440);
				rt513.e.push_back(e1);
				rt513.e.push_back(e248);
				rt513.e.push_back(e249);
				rt513.e.push_back(e59);
				rt513.e.push_back(e47);
				rt513.e.push_back(e3);
				rt513.calc_arity(nullptr);
				sprawformtree ft512 = std::make_shared<raw_form_tree>(elem::NONE, rt513);
				sprawformtree ft510 = std::make_shared<raw_form_tree>(elem::EXISTS, ft511, ft512);
				sprawformtree ft509 = std::make_shared<raw_form_tree>(elem::NOT, ft510);
				sprawformtree ft495 = std::make_shared<raw_form_tree>(elem::AND, ft496, ft509);
				raw_term rt516;
				rt516.neg = false;
				rt516.extype = raw_term::REL;
				rt516.e.push_back(e449);
				rt516.e.push_back(e1);
				rt516.e.push_back(e248);
				rt516.e.push_back(e249);
				rt516.e.push_back(e59);
				rt516.e.push_back(e3);
				rt516.calc_arity(nullptr);
				sprawformtree ft515 = std::make_shared<raw_form_tree>(elem::NONE, rt516);
				sprawformtree ft514 = std::make_shared<raw_form_tree>(elem::NOT, ft515);
				sprawformtree ft494 = std::make_shared<raw_form_tree>(elem::AND, ft495, ft514);
				raw_rule rr517;
				rr517.h.push_back(rt493);
				rr517.set_prft(ft494);
				raw_term rt518;
				rt518.neg = false;
				rt518.extype = raw_term::REL;
				rt518.e.push_back(e435);
				rt518.e.push_back(e1);
				rt518.e.push_back(e248);
				rt518.e.push_back(e249);
				rt518.e.push_back(e250);
				rt518.e.push_back(e256);
				rt518.e.push_back(e59);
				rt518.e.push_back(e47);
				rt518.e.push_back(e3);
				rt518.calc_arity(nullptr);
				raw_term rt525;
				rt525.neg = false;
				rt525.extype = raw_term::REL;
				rt525.e.push_back(e155);
				rt525.e.push_back(e1);
				rt525.e.push_back(e233);
				rt525.e.push_back(e500);
				rt525.e.push_back(e250);
				rt525.e.push_back(e3);
				rt525.calc_arity(nullptr);
				sprawformtree ft524 = std::make_shared<raw_form_tree>(elem::NONE, rt525);
				raw_term rt527;
				rt527.neg = false;
				rt527.extype = raw_term::REL;
				rt527.e.push_back(e155);
				rt527.e.push_back(e1);
				rt527.e.push_back(e234);
				rt527.e.push_back(e452);
				rt527.e.push_back(e256);
				rt527.e.push_back(e3);
				rt527.calc_arity(nullptr);
				sprawformtree ft526 = std::make_shared<raw_form_tree>(elem::NONE, rt527);
				sprawformtree ft523 = std::make_shared<raw_form_tree>(elem::AND, ft524, ft526);
				raw_term rt529;
				rt529.neg = false;
				rt529.extype = raw_term::REL;
				rt529.e.push_back(e435);
				rt529.e.push_back(e1);
				rt529.e.push_back(e248);
				rt529.e.push_back(e249);
				rt529.e.push_back(e233);
				rt529.e.push_back(e234);
				rt529.e.push_back(e59);
				rt529.e.push_back(e47);
				rt529.e.push_back(e3);
				rt529.calc_arity(nullptr);
				sprawformtree ft528 = std::make_shared<raw_form_tree>(elem::NONE, rt529);
				sprawformtree ft522 = std::make_shared<raw_form_tree>(elem::AND, ft523, ft528);
				raw_term rt532;
				rt532.neg = false;
				rt532.extype = raw_term::EQ;
				rt532.e.push_back(e500);
				rt532.e.push_back(e109);
				rt532.e.push_back(e59);
				rt532.calc_arity(nullptr);
				sprawformtree ft531 = std::make_shared<raw_form_tree>(elem::NONE, rt532);
				sprawformtree ft530 = std::make_shared<raw_form_tree>(elem::NOT, ft531);
				sprawformtree ft521 = std::make_shared<raw_form_tree>(elem::AND, ft522, ft530);
				sprawformtree ft535 = std::make_shared<raw_form_tree>(elem::VAR, e47);
				raw_term rt537;
				rt537.neg = false;
				rt537.extype = raw_term::REL;
				rt537.e.push_back(e440);
				rt537.e.push_back(e1);
				rt537.e.push_back(e248);
				rt537.e.push_back(e249);
				rt537.e.push_back(e59);
				rt537.e.push_back(e47);
				rt537.e.push_back(e3);
				rt537.calc_arity(nullptr);
				sprawformtree ft536 = std::make_shared<raw_form_tree>(elem::NONE, rt537);
				sprawformtree ft534 = std::make_shared<raw_form_tree>(elem::EXISTS, ft535, ft536);
				sprawformtree ft533 = std::make_shared<raw_form_tree>(elem::NOT, ft534);
				sprawformtree ft520 = std::make_shared<raw_form_tree>(elem::AND, ft521, ft533);
				raw_term rt540;
				rt540.neg = false;
				rt540.extype = raw_term::REL;
				rt540.e.push_back(e449);
				rt540.e.push_back(e1);
				rt540.e.push_back(e248);
				rt540.e.push_back(e249);
				rt540.e.push_back(e59);
				rt540.e.push_back(e3);
				rt540.calc_arity(nullptr);
				sprawformtree ft539 = std::make_shared<raw_form_tree>(elem::NONE, rt540);
				sprawformtree ft538 = std::make_shared<raw_form_tree>(elem::NOT, ft539);
				sprawformtree ft519 = std::make_shared<raw_form_tree>(elem::AND, ft520, ft538);
				raw_rule rr541;
				rr541.h.push_back(rt518);
				rr541.set_prft(ft519);
				raw_term rt542;
				rt542.neg = false;
				rt542.extype = raw_term::REL;
				rt542.e.push_back(e440);
				rt542.e.push_back(e1);
				rt542.e.push_back(e248);
				rt542.e.push_back(e249);
				rt542.e.push_back(e59);
				rt542.e.push_back(e47);
				rt542.e.push_back(e3);
				rt542.calc_arity(nullptr);
				raw_term rt548;
				rt548.neg = false;
				rt548.extype = raw_term::REL;
				rt548.e.push_back(e435);
				rt548.e.push_back(e1);
				rt548.e.push_back(e248);
				rt548.e.push_back(e249);
				rt548.e.push_back(e233);
				rt548.e.push_back(e234);
				rt548.e.push_back(e59);
				rt548.e.push_back(e47);
				rt548.e.push_back(e3);
				rt548.calc_arity(nullptr);
				sprawformtree ft547 = std::make_shared<raw_form_tree>(elem::NONE, rt548);
				raw_term rt550;
				rt550.neg = false;
				rt550.extype = raw_term::REL;
				rt550.e.push_back(e155);
				rt550.e.push_back(e1);
				rt550.e.push_back(e233);
				rt550.e.push_back(e3);
				rt550.calc_arity(nullptr);
				sprawformtree ft549 = std::make_shared<raw_form_tree>(elem::NONE, rt550);
				sprawformtree ft546 = std::make_shared<raw_form_tree>(elem::AND, ft547, ft549);
				raw_term rt552;
				rt552.neg = false;
				rt552.extype = raw_term::REL;
				rt552.e.push_back(e155);
				rt552.e.push_back(e1);
				rt552.e.push_back(e234);
				rt552.e.push_back(e3);
				rt552.calc_arity(nullptr);
				sprawformtree ft551 = std::make_shared<raw_form_tree>(elem::NONE, rt552);
				sprawformtree ft545 = std::make_shared<raw_form_tree>(elem::AND, ft546, ft551);
				sprawformtree ft555 = std::make_shared<raw_form_tree>(elem::VAR, e47);
				raw_term rt557;
				rt557.neg = false;
				rt557.extype = raw_term::REL;
				rt557.e.push_back(e440);
				rt557.e.push_back(e1);
				rt557.e.push_back(e248);
				rt557.e.push_back(e249);
				rt557.e.push_back(e59);
				rt557.e.push_back(e47);
				rt557.e.push_back(e3);
				rt557.calc_arity(nullptr);
				sprawformtree ft556 = std::make_shared<raw_form_tree>(elem::NONE, rt557);
				sprawformtree ft554 = std::make_shared<raw_form_tree>(elem::EXISTS, ft555, ft556);
				sprawformtree ft553 = std::make_shared<raw_form_tree>(elem::NOT, ft554);
				sprawformtree ft544 = std::make_shared<raw_form_tree>(elem::AND, ft545, ft553);
				raw_term rt560;
				rt560.neg = false;
				rt560.extype = raw_term::REL;
				rt560.e.push_back(e449);
				rt560.e.push_back(e1);
				rt560.e.push_back(e248);
				rt560.e.push_back(e249);
				rt560.e.push_back(e59);
				rt560.e.push_back(e3);
				rt560.calc_arity(nullptr);
				sprawformtree ft559 = std::make_shared<raw_form_tree>(elem::NONE, rt560);
				sprawformtree ft558 = std::make_shared<raw_form_tree>(elem::NOT, ft559);
				sprawformtree ft543 = std::make_shared<raw_form_tree>(elem::AND, ft544, ft558);
				raw_rule rr561;
				rr561.h.push_back(rt542);
				rr561.set_prft(ft543);
				raw_term rt562;
				rt562.neg = false;
				rt562.extype = raw_term::REL;
				rt562.e.push_back(e440);
				rt562.e.push_back(e1);
				rt562.e.push_back(e248);
				rt562.e.push_back(e249);
				rt562.e.push_back(e59);
				rt562.e.push_back(e47);
				rt562.e.push_back(e3);
				rt562.calc_arity(nullptr);
				raw_term rt569;
				rt569.neg = false;
				rt569.extype = raw_term::REL;
				rt569.e.push_back(e158);
				rt569.e.push_back(e1);
				rt569.e.push_back(e47);
				rt569.e.push_back(e3);
				rt569.calc_arity(nullptr);
				sprawformtree ft568 = std::make_shared<raw_form_tree>(elem::NONE, rt569);
				raw_term rt571;
				rt571.neg = false;
				rt571.extype = raw_term::REL;
				rt571.e.push_back(e435);
				rt571.e.push_back(e1);
				rt571.e.push_back(e248);
				rt571.e.push_back(e249);
				rt571.e.push_back(e233);
				rt571.e.push_back(e234);
				rt571.e.push_back(e59);
				rt571.e.push_back(e3);
				rt571.calc_arity(nullptr);
				sprawformtree ft570 = std::make_shared<raw_form_tree>(elem::NONE, rt571);
				sprawformtree ft567 = std::make_shared<raw_form_tree>(elem::AND, ft568, ft570);
				raw_term rt573;
				rt573.neg = false;
				rt573.extype = raw_term::REL;
				rt573.e.push_back(e155);
				rt573.e.push_back(e1);
				rt573.e.push_back(e233);
				rt573.e.push_back(e3);
				rt573.calc_arity(nullptr);
				sprawformtree ft572 = std::make_shared<raw_form_tree>(elem::NONE, rt573);
				sprawformtree ft566 = std::make_shared<raw_form_tree>(elem::AND, ft567, ft572);
				raw_term rt575;
				rt575.neg = false;
				rt575.extype = raw_term::REL;
				rt575.e.push_back(e155);
				rt575.e.push_back(e1);
				rt575.e.push_back(e234);
				rt575.e.push_back(e3);
				rt575.calc_arity(nullptr);
				sprawformtree ft574 = std::make_shared<raw_form_tree>(elem::NONE, rt575);
				sprawformtree ft565 = std::make_shared<raw_form_tree>(elem::AND, ft566, ft574);
				sprawformtree ft578 = std::make_shared<raw_form_tree>(elem::VAR, e47);
				raw_term rt580;
				rt580.neg = false;
				rt580.extype = raw_term::REL;
				rt580.e.push_back(e440);
				rt580.e.push_back(e1);
				rt580.e.push_back(e248);
				rt580.e.push_back(e249);
				rt580.e.push_back(e59);
				rt580.e.push_back(e47);
				rt580.e.push_back(e3);
				rt580.calc_arity(nullptr);
				sprawformtree ft579 = std::make_shared<raw_form_tree>(elem::NONE, rt580);
				sprawformtree ft577 = std::make_shared<raw_form_tree>(elem::EXISTS, ft578, ft579);
				sprawformtree ft576 = std::make_shared<raw_form_tree>(elem::NOT, ft577);
				sprawformtree ft564 = std::make_shared<raw_form_tree>(elem::AND, ft565, ft576);
				raw_term rt583;
				rt583.neg = false;
				rt583.extype = raw_term::REL;
				rt583.e.push_back(e449);
				rt583.e.push_back(e1);
				rt583.e.push_back(e248);
				rt583.e.push_back(e249);
				rt583.e.push_back(e59);
				rt583.e.push_back(e3);
				rt583.calc_arity(nullptr);
				sprawformtree ft582 = std::make_shared<raw_form_tree>(elem::NONE, rt583);
				sprawformtree ft581 = std::make_shared<raw_form_tree>(elem::NOT, ft582);
				sprawformtree ft563 = std::make_shared<raw_form_tree>(elem::AND, ft564, ft581);
				raw_rule rr584;
				rr584.h.push_back(rt562);
				rr584.set_prft(ft563);
				raw_term rt585;
				rt585.neg = true;
				rt585.extype = raw_term::REL;
				rt585.e.push_back(e435);
				rt585.e.push_back(e1);
				rt585.e.push_back(e248);
				rt585.e.push_back(e249);
				rt585.e.push_back(e233);
				rt585.e.push_back(e234);
				rt585.e.push_back(e59);
				rt585.e.push_back(e3);
				rt585.calc_arity(nullptr);
				raw_term rt586;
				rt586.neg = true;
				rt586.extype = raw_term::REL;
				rt586.e.push_back(e435);
				rt586.e.push_back(e1);
				rt586.e.push_back(e248);
				rt586.e.push_back(e249);
				rt586.e.push_back(e233);
				rt586.e.push_back(e234);
				rt586.e.push_back(e59);
				rt586.e.push_back(e47);
				rt586.e.push_back(e3);
				rt586.calc_arity(nullptr);
				raw_term rt589;
				rt589.neg = false;
				rt589.extype = raw_term::REL;
				rt589.e.push_back(e440);
				rt589.e.push_back(e1);
				rt589.e.push_back(e248);
				rt589.e.push_back(e249);
				rt589.e.push_back(e59);
				rt589.e.push_back(e151);
				rt589.e.push_back(e3);
				rt589.calc_arity(nullptr);
				sprawformtree ft588 = std::make_shared<raw_form_tree>(elem::NONE, rt589);
				raw_term rt591;
				rt591.neg = false;
				rt591.extype = raw_term::REL;
				rt591.e.push_back(e449);
				rt591.e.push_back(e1);
				rt591.e.push_back(e248);
				rt591.e.push_back(e249);
				rt591.e.push_back(e59);
				rt591.e.push_back(e3);
				rt591.calc_arity(nullptr);
				sprawformtree ft590 = std::make_shared<raw_form_tree>(elem::NONE, rt591);
				sprawformtree ft587 = std::make_shared<raw_form_tree>(elem::ALT, ft588, ft590);
				raw_rule rr592;
				rr592.h.push_back(rt585);
				rr592.h.push_back(rt586);
				rr592.set_prft(ft587);
				elem e593;
				e593.type = elem::SYM;
				e593.e = d.get_lexeme("ASSOC_LIST0");
				elem e594;
				e594.type = elem::VAR;
				e594.e = d.get_lexeme("?ts");
				elem e595;
				e595.type = elem::VAR;
				e595.e = d.get_lexeme("?us");
				raw_term rt596;
				rt596.neg = false;
				rt596.extype = raw_term::REL;
				rt596.e.push_back(e593);
				rt596.e.push_back(e1);
				rt596.e.push_back(e594);
				rt596.e.push_back(e233);
				rt596.e.push_back(e234);
				rt596.e.push_back(e594);
				rt596.e.push_back(e595);
				rt596.e.push_back(e3);
				rt596.calc_arity(nullptr);
				elem e600;
				e600.type = elem::SYM;
				e600.e = d.get_lexeme("ASSOC_LIST");
				raw_term rt601;
				rt601.neg = false;
				rt601.extype = raw_term::REL;
				rt601.e.push_back(e600);
				rt601.e.push_back(e1);
				rt601.e.push_back(e233);
				rt601.e.push_back(e234);
				rt601.e.push_back(e594);
				rt601.e.push_back(e3);
				rt601.calc_arity(nullptr);
				sprawformtree ft599 = std::make_shared<raw_form_tree>(elem::NONE, rt601);
				raw_term rt603;
				rt603.neg = false;
				rt603.extype = raw_term::REL;
				rt603.e.push_back(e155);
				rt603.e.push_back(e1);
				rt603.e.push_back(e595);
				rt603.e.push_back(e3);
				rt603.calc_arity(nullptr);
				sprawformtree ft602 = std::make_shared<raw_form_tree>(elem::NONE, rt603);
				sprawformtree ft598 = std::make_shared<raw_form_tree>(elem::AND, ft599, ft602);
				sprawformtree ft606 = std::make_shared<raw_form_tree>(elem::VAR, e151);
				raw_term rt608;
				rt608.neg = false;
				rt608.extype = raw_term::REL;
				rt608.e.push_back(e600);
				rt608.e.push_back(e1);
				rt608.e.push_back(e233);
				rt608.e.push_back(e234);
				rt608.e.push_back(e594);
				rt608.e.push_back(e151);
				rt608.e.push_back(e3);
				rt608.calc_arity(nullptr);
				sprawformtree ft607 = std::make_shared<raw_form_tree>(elem::NONE, rt608);
				sprawformtree ft605 = std::make_shared<raw_form_tree>(elem::EXISTS, ft606, ft607);
				sprawformtree ft604 = std::make_shared<raw_form_tree>(elem::NOT, ft605);
				sprawformtree ft597 = std::make_shared<raw_form_tree>(elem::AND, ft598, ft604);
				raw_rule rr609;
				rr609.h.push_back(rt596);
				rr609.set_prft(ft597);
				elem e610;
				e610.type = elem::VAR;
				e610.e = d.get_lexeme("?ts_hd");
				raw_term rt611;
				rt611.neg = false;
				rt611.extype = raw_term::REL;
				rt611.e.push_back(e440);
				rt611.e.push_back(e1);
				rt611.e.push_back(e233);
				rt611.e.push_back(e234);
				rt611.e.push_back(e610);
				rt611.e.push_back(e3);
				rt611.calc_arity(nullptr);
				elem e612;
				e612.type = elem::SYM;
				e612.e = d.get_lexeme("ASSOC_LIST1");
				elem e613;
				e613.type = elem::VAR;
				e613.e = d.get_lexeme("?ots");
				raw_term rt614;
				rt614.neg = false;
				rt614.extype = raw_term::REL;
				rt614.e.push_back(e612);
				rt614.e.push_back(e1);
				rt614.e.push_back(e613);
				rt614.e.push_back(e233);
				rt614.e.push_back(e234);
				rt614.e.push_back(e594);
				rt614.e.push_back(e595);
				rt614.e.push_back(e3);
				rt614.calc_arity(nullptr);
				raw_term rt618;
				rt618.neg = false;
				rt618.extype = raw_term::REL;
				rt618.e.push_back(e593);
				rt618.e.push_back(e1);
				rt618.e.push_back(e613);
				rt618.e.push_back(e233);
				rt618.e.push_back(e234);
				rt618.e.push_back(e594);
				rt618.e.push_back(e595);
				rt618.e.push_back(e3);
				rt618.calc_arity(nullptr);
				sprawformtree ft617 = std::make_shared<raw_form_tree>(elem::NONE, rt618);
				elem e620;
				e620.type = elem::VAR;
				e620.e = d.get_lexeme("?ts_tl");
				raw_term rt621;
				rt621.neg = false;
				rt621.extype = raw_term::REL;
				rt621.e.push_back(e155);
				rt621.e.push_back(e1);
				rt621.e.push_back(e594);
				rt621.e.push_back(e610);
				rt621.e.push_back(e620);
				rt621.e.push_back(e3);
				rt621.calc_arity(nullptr);
				sprawformtree ft619 = std::make_shared<raw_form_tree>(elem::NONE, rt621);
				sprawformtree ft616 = std::make_shared<raw_form_tree>(elem::AND, ft617, ft619);
				sprawformtree ft624 = std::make_shared<raw_form_tree>(elem::VAR, e151);
				raw_term rt626;
				rt626.neg = false;
				rt626.extype = raw_term::REL;
				rt626.e.push_back(e600);
				rt626.e.push_back(e1);
				rt626.e.push_back(e233);
				rt626.e.push_back(e234);
				rt626.e.push_back(e613);
				rt626.e.push_back(e151);
				rt626.e.push_back(e3);
				rt626.calc_arity(nullptr);
				sprawformtree ft625 = std::make_shared<raw_form_tree>(elem::NONE, rt626);
				sprawformtree ft623 = std::make_shared<raw_form_tree>(elem::EXISTS, ft624, ft625);
				sprawformtree ft622 = std::make_shared<raw_form_tree>(elem::NOT, ft623);
				sprawformtree ft615 = std::make_shared<raw_form_tree>(elem::AND, ft616, ft622);
				raw_rule rr627;
				rr627.h.push_back(rt611);
				rr627.h.push_back(rt614);
				rr627.set_prft(ft615);
				elem e628;
				e628.type = elem::VAR;
				e628.e = d.get_lexeme("?nus");
				raw_term rt629;
				rt629.neg = false;
				rt629.extype = raw_term::REL;
				rt629.e.push_back(e593);
				rt629.e.push_back(e1);
				rt629.e.push_back(e613);
				rt629.e.push_back(e233);
				rt629.e.push_back(e234);
				rt629.e.push_back(e620);
				rt629.e.push_back(e628);
				rt629.e.push_back(e3);
				rt629.calc_arity(nullptr);
				raw_term rt635;
				rt635.neg = false;
				rt635.extype = raw_term::REL;
				rt635.e.push_back(e612);
				rt635.e.push_back(e1);
				rt635.e.push_back(e613);
				rt635.e.push_back(e233);
				rt635.e.push_back(e234);
				rt635.e.push_back(e594);
				rt635.e.push_back(e595);
				rt635.e.push_back(e3);
				rt635.calc_arity(nullptr);
				sprawformtree ft634 = std::make_shared<raw_form_tree>(elem::NONE, rt635);
				raw_term rt637;
				rt637.neg = false;
				rt637.extype = raw_term::REL;
				rt637.e.push_back(e155);
				rt637.e.push_back(e1);
				rt637.e.push_back(e594);
				rt637.e.push_back(e610);
				rt637.e.push_back(e620);
				rt637.e.push_back(e3);
				rt637.calc_arity(nullptr);
				sprawformtree ft636 = std::make_shared<raw_form_tree>(elem::NONE, rt637);
				sprawformtree ft633 = std::make_shared<raw_form_tree>(elem::AND, ft634, ft636);
				elem e639;
				e639.type = elem::VAR;
				e639.e = d.get_lexeme("?nus_hd");
				raw_term rt640;
				rt640.neg = false;
				rt640.extype = raw_term::REL;
				rt640.e.push_back(e440);
				rt640.e.push_back(e1);
				rt640.e.push_back(e233);
				rt640.e.push_back(e234);
				rt640.e.push_back(e610);
				rt640.e.push_back(e639);
				rt640.e.push_back(e3);
				rt640.calc_arity(nullptr);
				sprawformtree ft638 = std::make_shared<raw_form_tree>(elem::NONE, rt640);
				sprawformtree ft632 = std::make_shared<raw_form_tree>(elem::AND, ft633, ft638);
				raw_term rt642;
				rt642.neg = false;
				rt642.extype = raw_term::REL;
				rt642.e.push_back(e155);
				rt642.e.push_back(e1);
				rt642.e.push_back(e628);
				rt642.e.push_back(e639);
				rt642.e.push_back(e595);
				rt642.e.push_back(e3);
				rt642.calc_arity(nullptr);
				sprawformtree ft641 = std::make_shared<raw_form_tree>(elem::NONE, rt642);
				sprawformtree ft631 = std::make_shared<raw_form_tree>(elem::AND, ft632, ft641);
				sprawformtree ft645 = std::make_shared<raw_form_tree>(elem::VAR, e151);
				raw_term rt647;
				rt647.neg = false;
				rt647.extype = raw_term::REL;
				rt647.e.push_back(e600);
				rt647.e.push_back(e1);
				rt647.e.push_back(e233);
				rt647.e.push_back(e234);
				rt647.e.push_back(e613);
				rt647.e.push_back(e151);
				rt647.e.push_back(e3);
				rt647.calc_arity(nullptr);
				sprawformtree ft646 = std::make_shared<raw_form_tree>(elem::NONE, rt647);
				sprawformtree ft644 = std::make_shared<raw_form_tree>(elem::EXISTS, ft645, ft646);
				sprawformtree ft643 = std::make_shared<raw_form_tree>(elem::NOT, ft644);
				sprawformtree ft630 = std::make_shared<raw_form_tree>(elem::AND, ft631, ft643);
				raw_rule rr648;
				rr648.h.push_back(rt629);
				rr648.set_prft(ft630);
				raw_term rt649;
				rt649.neg = false;
				rt649.extype = raw_term::REL;
				rt649.e.push_back(e334);
				rt649.e.push_back(e1);
				rt649.e.push_back(e595);
				rt649.e.push_back(e3);
				rt649.calc_arity(nullptr);
				elem e650;
				e650.type = elem::SYM;
				e650.e = d.get_lexeme("ASSOC_LIST2");
				raw_term rt651;
				rt651.neg = false;
				rt651.extype = raw_term::REL;
				rt651.e.push_back(e650);
				rt651.e.push_back(e1);
				rt651.e.push_back(e613);
				rt651.e.push_back(e233);
				rt651.e.push_back(e234);
				rt651.e.push_back(e594);
				rt651.e.push_back(e595);
				rt651.e.push_back(e3);
				rt651.calc_arity(nullptr);
				raw_term rt655;
				rt655.neg = false;
				rt655.extype = raw_term::REL;
				rt655.e.push_back(e593);
				rt655.e.push_back(e1);
				rt655.e.push_back(e613);
				rt655.e.push_back(e233);
				rt655.e.push_back(e234);
				rt655.e.push_back(e594);
				rt655.e.push_back(e595);
				rt655.e.push_back(e3);
				rt655.calc_arity(nullptr);
				sprawformtree ft654 = std::make_shared<raw_form_tree>(elem::NONE, rt655);
				raw_term rt657;
				rt657.neg = false;
				rt657.extype = raw_term::REL;
				rt657.e.push_back(e155);
				rt657.e.push_back(e1);
				rt657.e.push_back(e594);
				rt657.e.push_back(e3);
				rt657.calc_arity(nullptr);
				sprawformtree ft656 = std::make_shared<raw_form_tree>(elem::NONE, rt657);
				sprawformtree ft653 = std::make_shared<raw_form_tree>(elem::AND, ft654, ft656);
				sprawformtree ft660 = std::make_shared<raw_form_tree>(elem::VAR, e151);
				raw_term rt662;
				rt662.neg = false;
				rt662.extype = raw_term::REL;
				rt662.e.push_back(e600);
				rt662.e.push_back(e1);
				rt662.e.push_back(e233);
				rt662.e.push_back(e234);
				rt662.e.push_back(e613);
				rt662.e.push_back(e151);
				rt662.e.push_back(e3);
				rt662.calc_arity(nullptr);
				sprawformtree ft661 = std::make_shared<raw_form_tree>(elem::NONE, rt662);
				sprawformtree ft659 = std::make_shared<raw_form_tree>(elem::EXISTS, ft660, ft661);
				sprawformtree ft658 = std::make_shared<raw_form_tree>(elem::NOT, ft659);
				sprawformtree ft652 = std::make_shared<raw_form_tree>(elem::AND, ft653, ft658);
				raw_rule rr663;
				rr663.h.push_back(rt649);
				rr663.h.push_back(rt651);
				rr663.set_prft(ft652);
				raw_term rt664;
				rt664.neg = false;
				rt664.extype = raw_term::REL;
				rt664.e.push_back(e600);
				rt664.e.push_back(e1);
				rt664.e.push_back(e233);
				rt664.e.push_back(e234);
				rt664.e.push_back(e613);
				rt664.e.push_back(e628);
				rt664.e.push_back(e3);
				rt664.calc_arity(nullptr);
				raw_term rt669;
				rt669.neg = false;
				rt669.extype = raw_term::REL;
				rt669.e.push_back(e650);
				rt669.e.push_back(e1);
				rt669.e.push_back(e613);
				rt669.e.push_back(e233);
				rt669.e.push_back(e234);
				rt669.e.push_back(e594);
				rt669.e.push_back(e595);
				rt669.e.push_back(e3);
				rt669.calc_arity(nullptr);
				sprawformtree ft668 = std::make_shared<raw_form_tree>(elem::NONE, rt669);
				raw_term rt671;
				rt671.neg = false;
				rt671.extype = raw_term::REL;
				rt671.e.push_back(e347);
				rt671.e.push_back(e1);
				rt671.e.push_back(e595);
				rt671.e.push_back(e628);
				rt671.e.push_back(e3);
				rt671.calc_arity(nullptr);
				sprawformtree ft670 = std::make_shared<raw_form_tree>(elem::NONE, rt671);
				sprawformtree ft667 = std::make_shared<raw_form_tree>(elem::AND, ft668, ft670);
				raw_term rt673;
				rt673.neg = false;
				rt673.extype = raw_term::REL;
				rt673.e.push_back(e155);
				rt673.e.push_back(e1);
				rt673.e.push_back(e594);
				rt673.e.push_back(e3);
				rt673.calc_arity(nullptr);
				sprawformtree ft672 = std::make_shared<raw_form_tree>(elem::NONE, rt673);
				sprawformtree ft666 = std::make_shared<raw_form_tree>(elem::AND, ft667, ft672);
				sprawformtree ft676 = std::make_shared<raw_form_tree>(elem::VAR, e151);
				raw_term rt678;
				rt678.neg = false;
				rt678.extype = raw_term::REL;
				rt678.e.push_back(e600);
				rt678.e.push_back(e1);
				rt678.e.push_back(e233);
				rt678.e.push_back(e234);
				rt678.e.push_back(e613);
				rt678.e.push_back(e151);
				rt678.e.push_back(e3);
				rt678.calc_arity(nullptr);
				sprawformtree ft677 = std::make_shared<raw_form_tree>(elem::NONE, rt678);
				sprawformtree ft675 = std::make_shared<raw_form_tree>(elem::EXISTS, ft676, ft677);
				sprawformtree ft674 = std::make_shared<raw_form_tree>(elem::NOT, ft675);
				sprawformtree ft665 = std::make_shared<raw_form_tree>(elem::AND, ft666, ft674);
				raw_rule rr679;
				rr679.h.push_back(rt664);
				rr679.set_prft(ft665);
				raw_term rt680;
				rt680.neg = true;
				rt680.extype = raw_term::REL;
				rt680.e.push_back(e593);
				rt680.e.push_back(e1);
				rt680.e.push_back(e613);
				rt680.e.push_back(e233);
				rt680.e.push_back(e234);
				rt680.e.push_back(e620);
				rt680.e.push_back(e628);
				rt680.e.push_back(e3);
				rt680.calc_arity(nullptr);
				raw_term rt681;
				rt681.neg = true;
				rt681.extype = raw_term::REL;
				rt681.e.push_back(e612);
				rt681.e.push_back(e1);
				rt681.e.push_back(e613);
				rt681.e.push_back(e233);
				rt681.e.push_back(e234);
				rt681.e.push_back(e594);
				rt681.e.push_back(e595);
				rt681.e.push_back(e3);
				rt681.calc_arity(nullptr);
				raw_term rt682;
				rt682.neg = true;
				rt682.extype = raw_term::REL;
				rt682.e.push_back(e650);
				rt682.e.push_back(e1);
				rt682.e.push_back(e613);
				rt682.e.push_back(e233);
				rt682.e.push_back(e234);
				rt682.e.push_back(e594);
				rt682.e.push_back(e595);
				rt682.e.push_back(e3);
				rt682.calc_arity(nullptr);
				raw_term rt684;
				rt684.neg = false;
				rt684.extype = raw_term::REL;
				rt684.e.push_back(e600);
				rt684.e.push_back(e1);
				rt684.e.push_back(e233);
				rt684.e.push_back(e234);
				rt684.e.push_back(e613);
				rt684.e.push_back(e151);
				rt684.e.push_back(e3);
				rt684.calc_arity(nullptr);
				sprawformtree ft683 = std::make_shared<raw_form_tree>(elem::NONE, rt684);
				raw_rule rr685;
				rr685.h.push_back(rt680);
				rr685.h.push_back(rt681);
				rr685.h.push_back(rt682);
				rr685.set_prft(ft683);
				elem e686;
				e686.type = elem::SYM;
				e686.e = d.get_lexeme("IS_CONSISTENT0");
				raw_term rt687;
				rt687.neg = false;
				rt687.extype = raw_term::REL;
				rt687.e.push_back(e686);
				rt687.e.push_back(e1);
				rt687.e.push_back(e233);
				rt687.e.push_back(e234);
				rt687.e.push_back(e233);
				rt687.e.push_back(e234);
				rt687.e.push_back(e59);
				rt687.e.push_back(e47);
				rt687.e.push_back(e3);
				rt687.calc_arity(nullptr);
				elem e691;
				e691.type = elem::SYM;
				e691.e = d.get_lexeme("IS_ASSOC_CONSISTENT");
				raw_term rt692;
				rt692.neg = false;
				rt692.extype = raw_term::REL;
				rt692.e.push_back(e691);
				rt692.e.push_back(e1);
				rt692.e.push_back(e233);
				rt692.e.push_back(e234);
				rt692.e.push_back(e59);
				rt692.e.push_back(e47);
				rt692.e.push_back(e3);
				rt692.calc_arity(nullptr);
				sprawformtree ft690 = std::make_shared<raw_form_tree>(elem::NONE, rt692);
				elem e695;
				e695.type = elem::SYM;
				e695.e = d.get_lexeme("CONSISTENT");
				raw_term rt696;
				rt696.neg = false;
				rt696.extype = raw_term::REL;
				rt696.e.push_back(e695);
				rt696.e.push_back(e1);
				rt696.e.push_back(e233);
				rt696.e.push_back(e234);
				rt696.e.push_back(e59);
				rt696.e.push_back(e47);
				rt696.e.push_back(e3);
				rt696.calc_arity(nullptr);
				sprawformtree ft694 = std::make_shared<raw_form_tree>(elem::NONE, rt696);
				sprawformtree ft693 = std::make_shared<raw_form_tree>(elem::NOT, ft694);
				sprawformtree ft689 = std::make_shared<raw_form_tree>(elem::AND, ft690, ft693);
				elem e699;
				e699.type = elem::SYM;
				e699.e = d.get_lexeme("NOT_CONSISTENT");
				raw_term rt700;
				rt700.neg = false;
				rt700.extype = raw_term::REL;
				rt700.e.push_back(e699);
				rt700.e.push_back(e1);
				rt700.e.push_back(e233);
				rt700.e.push_back(e234);
				rt700.e.push_back(e59);
				rt700.e.push_back(e47);
				rt700.e.push_back(e3);
				rt700.calc_arity(nullptr);
				sprawformtree ft698 = std::make_shared<raw_form_tree>(elem::NONE, rt700);
				sprawformtree ft697 = std::make_shared<raw_form_tree>(elem::NOT, ft698);
				sprawformtree ft688 = std::make_shared<raw_form_tree>(elem::AND, ft689, ft697);
				raw_rule rr701;
				rr701.h.push_back(rt687);
				rr701.set_prft(ft688);
				raw_term rt702;
				rt702.neg = false;
				rt702.extype = raw_term::REL;
				rt702.e.push_back(e686);
				rt702.e.push_back(e1);
				rt702.e.push_back(e248);
				rt702.e.push_back(e249);
				rt702.e.push_back(e250);
				rt702.e.push_back(e256);
				rt702.e.push_back(e59);
				rt702.e.push_back(e47);
				rt702.e.push_back(e3);
				rt702.calc_arity(nullptr);
				raw_term rt708;
				rt708.neg = false;
				rt708.extype = raw_term::REL;
				rt708.e.push_back(e150);
				rt708.e.push_back(e1);
				rt708.e.push_back(e233);
				rt708.e.push_back(e59);
				rt708.e.push_back(e250);
				rt708.e.push_back(e3);
				rt708.calc_arity(nullptr);
				sprawformtree ft707 = std::make_shared<raw_form_tree>(elem::NONE, rt708);
				raw_term rt710;
				rt710.neg = false;
				rt710.extype = raw_term::REL;
				rt710.e.push_back(e155);
				rt710.e.push_back(e1);
				rt710.e.push_back(e234);
				rt710.e.push_back(e47);
				rt710.e.push_back(e256);
				rt710.e.push_back(e3);
				rt710.calc_arity(nullptr);
				sprawformtree ft709 = std::make_shared<raw_form_tree>(elem::NONE, rt710);
				sprawformtree ft706 = std::make_shared<raw_form_tree>(elem::AND, ft707, ft709);
				raw_term rt712;
				rt712.neg = false;
				rt712.extype = raw_term::REL;
				rt712.e.push_back(e686);
				rt712.e.push_back(e1);
				rt712.e.push_back(e248);
				rt712.e.push_back(e249);
				rt712.e.push_back(e233);
				rt712.e.push_back(e234);
				rt712.e.push_back(e59);
				rt712.e.push_back(e47);
				rt712.e.push_back(e3);
				rt712.calc_arity(nullptr);
				sprawformtree ft711 = std::make_shared<raw_form_tree>(elem::NONE, rt712);
				sprawformtree ft705 = std::make_shared<raw_form_tree>(elem::AND, ft706, ft711);
				raw_term rt715;
				rt715.neg = false;
				rt715.extype = raw_term::REL;
				rt715.e.push_back(e695);
				rt715.e.push_back(e1);
				rt715.e.push_back(e248);
				rt715.e.push_back(e249);
				rt715.e.push_back(e59);
				rt715.e.push_back(e47);
				rt715.e.push_back(e3);
				rt715.calc_arity(nullptr);
				sprawformtree ft714 = std::make_shared<raw_form_tree>(elem::NONE, rt715);
				sprawformtree ft713 = std::make_shared<raw_form_tree>(elem::NOT, ft714);
				sprawformtree ft704 = std::make_shared<raw_form_tree>(elem::AND, ft705, ft713);
				raw_term rt718;
				rt718.neg = false;
				rt718.extype = raw_term::REL;
				rt718.e.push_back(e699);
				rt718.e.push_back(e1);
				rt718.e.push_back(e248);
				rt718.e.push_back(e249);
				rt718.e.push_back(e59);
				rt718.e.push_back(e47);
				rt718.e.push_back(e3);
				rt718.calc_arity(nullptr);
				sprawformtree ft717 = std::make_shared<raw_form_tree>(elem::NONE, rt718);
				sprawformtree ft716 = std::make_shared<raw_form_tree>(elem::NOT, ft717);
				sprawformtree ft703 = std::make_shared<raw_form_tree>(elem::AND, ft704, ft716);
				raw_rule rr719;
				rr719.h.push_back(rt702);
				rr719.set_prft(ft703);
				raw_term rt720;
				rt720.neg = false;
				rt720.extype = raw_term::REL;
				rt720.e.push_back(e686);
				rt720.e.push_back(e1);
				rt720.e.push_back(e248);
				rt720.e.push_back(e249);
				rt720.e.push_back(e250);
				rt720.e.push_back(e256);
				rt720.e.push_back(e59);
				rt720.e.push_back(e47);
				rt720.e.push_back(e3);
				rt720.calc_arity(nullptr);
				raw_term rt728;
				rt728.neg = false;
				rt728.extype = raw_term::REL;
				rt728.e.push_back(e150);
				rt728.e.push_back(e1);
				rt728.e.push_back(e233);
				rt728.e.push_back(e59);
				rt728.e.push_back(e250);
				rt728.e.push_back(e3);
				rt728.calc_arity(nullptr);
				sprawformtree ft727 = std::make_shared<raw_form_tree>(elem::NONE, rt728);
				sprawformtree ft726 = std::make_shared<raw_form_tree>(elem::NOT, ft727);
				raw_term rt730;
				rt730.neg = false;
				rt730.extype = raw_term::REL;
				rt730.e.push_back(e150);
				rt730.e.push_back(e1);
				rt730.e.push_back(e233);
				rt730.e.push_back(e259);
				rt730.e.push_back(e250);
				rt730.e.push_back(e3);
				rt730.calc_arity(nullptr);
				sprawformtree ft729 = std::make_shared<raw_form_tree>(elem::NONE, rt730);
				sprawformtree ft725 = std::make_shared<raw_form_tree>(elem::AND, ft726, ft729);
				elem e732;
				e732.type = elem::VAR;
				e732.e = d.get_lexeme("?ys_hd");
				raw_term rt733;
				rt733.neg = false;
				rt733.extype = raw_term::REL;
				rt733.e.push_back(e155);
				rt733.e.push_back(e1);
				rt733.e.push_back(e234);
				rt733.e.push_back(e732);
				rt733.e.push_back(e256);
				rt733.e.push_back(e3);
				rt733.calc_arity(nullptr);
				sprawformtree ft731 = std::make_shared<raw_form_tree>(elem::NONE, rt733);
				sprawformtree ft724 = std::make_shared<raw_form_tree>(elem::AND, ft725, ft731);
				raw_term rt735;
				rt735.neg = false;
				rt735.extype = raw_term::REL;
				rt735.e.push_back(e686);
				rt735.e.push_back(e1);
				rt735.e.push_back(e248);
				rt735.e.push_back(e249);
				rt735.e.push_back(e233);
				rt735.e.push_back(e234);
				rt735.e.push_back(e59);
				rt735.e.push_back(e47);
				rt735.e.push_back(e3);
				rt735.calc_arity(nullptr);
				sprawformtree ft734 = std::make_shared<raw_form_tree>(elem::NONE, rt735);
				sprawformtree ft723 = std::make_shared<raw_form_tree>(elem::AND, ft724, ft734);
				raw_term rt738;
				rt738.neg = false;
				rt738.extype = raw_term::REL;
				rt738.e.push_back(e695);
				rt738.e.push_back(e1);
				rt738.e.push_back(e248);
				rt738.e.push_back(e249);
				rt738.e.push_back(e59);
				rt738.e.push_back(e47);
				rt738.e.push_back(e3);
				rt738.calc_arity(nullptr);
				sprawformtree ft737 = std::make_shared<raw_form_tree>(elem::NONE, rt738);
				sprawformtree ft736 = std::make_shared<raw_form_tree>(elem::NOT, ft737);
				sprawformtree ft722 = std::make_shared<raw_form_tree>(elem::AND, ft723, ft736);
				raw_term rt741;
				rt741.neg = false;
				rt741.extype = raw_term::REL;
				rt741.e.push_back(e699);
				rt741.e.push_back(e1);
				rt741.e.push_back(e248);
				rt741.e.push_back(e249);
				rt741.e.push_back(e59);
				rt741.e.push_back(e47);
				rt741.e.push_back(e3);
				rt741.calc_arity(nullptr);
				sprawformtree ft740 = std::make_shared<raw_form_tree>(elem::NONE, rt741);
				sprawformtree ft739 = std::make_shared<raw_form_tree>(elem::NOT, ft740);
				sprawformtree ft721 = std::make_shared<raw_form_tree>(elem::AND, ft722, ft739);
				raw_rule rr742;
				rr742.h.push_back(rt720);
				rr742.set_prft(ft721);
				raw_term rt743;
				rt743.neg = false;
				rt743.extype = raw_term::REL;
				rt743.e.push_back(e699);
				rt743.e.push_back(e1);
				rt743.e.push_back(e248);
				rt743.e.push_back(e249);
				rt743.e.push_back(e59);
				rt743.e.push_back(e47);
				rt743.e.push_back(e3);
				rt743.calc_arity(nullptr);
				raw_term rt750;
				rt750.neg = false;
				rt750.extype = raw_term::REL;
				rt750.e.push_back(e150);
				rt750.e.push_back(e1);
				rt750.e.push_back(e233);
				rt750.e.push_back(e59);
				rt750.e.push_back(e250);
				rt750.e.push_back(e3);
				rt750.calc_arity(nullptr);
				sprawformtree ft749 = std::make_shared<raw_form_tree>(elem::NONE, rt750);
				raw_term rt753;
				rt753.neg = false;
				rt753.extype = raw_term::REL;
				rt753.e.push_back(e155);
				rt753.e.push_back(e1);
				rt753.e.push_back(e234);
				rt753.e.push_back(e47);
				rt753.e.push_back(e256);
				rt753.e.push_back(e3);
				rt753.calc_arity(nullptr);
				sprawformtree ft752 = std::make_shared<raw_form_tree>(elem::NONE, rt753);
				sprawformtree ft751 = std::make_shared<raw_form_tree>(elem::NOT, ft752);
				sprawformtree ft748 = std::make_shared<raw_form_tree>(elem::AND, ft749, ft751);
				elem e755;
				e755.type = elem::VAR;
				e755.e = d.get_lexeme("?ay");
				raw_term rt756;
				rt756.neg = false;
				rt756.extype = raw_term::REL;
				rt756.e.push_back(e155);
				rt756.e.push_back(e1);
				rt756.e.push_back(e234);
				rt756.e.push_back(e755);
				rt756.e.push_back(e256);
				rt756.e.push_back(e3);
				rt756.calc_arity(nullptr);
				sprawformtree ft754 = std::make_shared<raw_form_tree>(elem::NONE, rt756);
				sprawformtree ft747 = std::make_shared<raw_form_tree>(elem::AND, ft748, ft754);
				raw_term rt758;
				rt758.neg = false;
				rt758.extype = raw_term::REL;
				rt758.e.push_back(e686);
				rt758.e.push_back(e1);
				rt758.e.push_back(e248);
				rt758.e.push_back(e249);
				rt758.e.push_back(e233);
				rt758.e.push_back(e234);
				rt758.e.push_back(e59);
				rt758.e.push_back(e47);
				rt758.e.push_back(e3);
				rt758.calc_arity(nullptr);
				sprawformtree ft757 = std::make_shared<raw_form_tree>(elem::NONE, rt758);
				sprawformtree ft746 = std::make_shared<raw_form_tree>(elem::AND, ft747, ft757);
				raw_term rt761;
				rt761.neg = false;
				rt761.extype = raw_term::REL;
				rt761.e.push_back(e695);
				rt761.e.push_back(e1);
				rt761.e.push_back(e248);
				rt761.e.push_back(e249);
				rt761.e.push_back(e59);
				rt761.e.push_back(e47);
				rt761.e.push_back(e3);
				rt761.calc_arity(nullptr);
				sprawformtree ft760 = std::make_shared<raw_form_tree>(elem::NONE, rt761);
				sprawformtree ft759 = std::make_shared<raw_form_tree>(elem::NOT, ft760);
				sprawformtree ft745 = std::make_shared<raw_form_tree>(elem::AND, ft746, ft759);
				raw_term rt764;
				rt764.neg = false;
				rt764.extype = raw_term::REL;
				rt764.e.push_back(e699);
				rt764.e.push_back(e1);
				rt764.e.push_back(e248);
				rt764.e.push_back(e249);
				rt764.e.push_back(e59);
				rt764.e.push_back(e47);
				rt764.e.push_back(e3);
				rt764.calc_arity(nullptr);
				sprawformtree ft763 = std::make_shared<raw_form_tree>(elem::NONE, rt764);
				sprawformtree ft762 = std::make_shared<raw_form_tree>(elem::NOT, ft763);
				sprawformtree ft744 = std::make_shared<raw_form_tree>(elem::AND, ft745, ft762);
				raw_rule rr765;
				rr765.h.push_back(rt743);
				rr765.set_prft(ft744);
				raw_term rt766;
				rt766.neg = false;
				rt766.extype = raw_term::REL;
				rt766.e.push_back(e695);
				rt766.e.push_back(e1);
				rt766.e.push_back(e248);
				rt766.e.push_back(e249);
				rt766.e.push_back(e59);
				rt766.e.push_back(e47);
				rt766.e.push_back(e3);
				rt766.calc_arity(nullptr);
				raw_term rt772;
				rt772.neg = false;
				rt772.extype = raw_term::REL;
				rt772.e.push_back(e686);
				rt772.e.push_back(e1);
				rt772.e.push_back(e248);
				rt772.e.push_back(e249);
				rt772.e.push_back(e233);
				rt772.e.push_back(e234);
				rt772.e.push_back(e59);
				rt772.e.push_back(e47);
				rt772.e.push_back(e3);
				rt772.calc_arity(nullptr);
				sprawformtree ft771 = std::make_shared<raw_form_tree>(elem::NONE, rt772);
				raw_term rt774;
				rt774.neg = false;
				rt774.extype = raw_term::REL;
				rt774.e.push_back(e150);
				rt774.e.push_back(e1);
				rt774.e.push_back(e233);
				rt774.e.push_back(e3);
				rt774.calc_arity(nullptr);
				sprawformtree ft773 = std::make_shared<raw_form_tree>(elem::NONE, rt774);
				sprawformtree ft770 = std::make_shared<raw_form_tree>(elem::AND, ft771, ft773);
				raw_term rt776;
				rt776.neg = false;
				rt776.extype = raw_term::REL;
				rt776.e.push_back(e155);
				rt776.e.push_back(e1);
				rt776.e.push_back(e234);
				rt776.e.push_back(e3);
				rt776.calc_arity(nullptr);
				sprawformtree ft775 = std::make_shared<raw_form_tree>(elem::NONE, rt776);
				sprawformtree ft769 = std::make_shared<raw_form_tree>(elem::AND, ft770, ft775);
				raw_term rt779;
				rt779.neg = false;
				rt779.extype = raw_term::REL;
				rt779.e.push_back(e695);
				rt779.e.push_back(e1);
				rt779.e.push_back(e248);
				rt779.e.push_back(e249);
				rt779.e.push_back(e59);
				rt779.e.push_back(e47);
				rt779.e.push_back(e3);
				rt779.calc_arity(nullptr);
				sprawformtree ft778 = std::make_shared<raw_form_tree>(elem::NONE, rt779);
				sprawformtree ft777 = std::make_shared<raw_form_tree>(elem::NOT, ft778);
				sprawformtree ft768 = std::make_shared<raw_form_tree>(elem::AND, ft769, ft777);
				raw_term rt782;
				rt782.neg = false;
				rt782.extype = raw_term::REL;
				rt782.e.push_back(e699);
				rt782.e.push_back(e1);
				rt782.e.push_back(e248);
				rt782.e.push_back(e249);
				rt782.e.push_back(e59);
				rt782.e.push_back(e47);
				rt782.e.push_back(e3);
				rt782.calc_arity(nullptr);
				sprawformtree ft781 = std::make_shared<raw_form_tree>(elem::NONE, rt782);
				sprawformtree ft780 = std::make_shared<raw_form_tree>(elem::NOT, ft781);
				sprawformtree ft767 = std::make_shared<raw_form_tree>(elem::AND, ft768, ft780);
				raw_rule rr783;
				rr783.h.push_back(rt766);
				rr783.set_prft(ft767);
				raw_term rt784;
				rt784.neg = true;
				rt784.extype = raw_term::REL;
				rt784.e.push_back(e686);
				rt784.e.push_back(e1);
				rt784.e.push_back(e248);
				rt784.e.push_back(e249);
				rt784.e.push_back(e250);
				rt784.e.push_back(e256);
				rt784.e.push_back(e59);
				rt784.e.push_back(e47);
				rt784.e.push_back(e3);
				rt784.calc_arity(nullptr);
				raw_term rt787;
				rt787.neg = false;
				rt787.extype = raw_term::REL;
				rt787.e.push_back(e695);
				rt787.e.push_back(e1);
				rt787.e.push_back(e248);
				rt787.e.push_back(e249);
				rt787.e.push_back(e59);
				rt787.e.push_back(e47);
				rt787.e.push_back(e3);
				rt787.calc_arity(nullptr);
				sprawformtree ft786 = std::make_shared<raw_form_tree>(elem::NONE, rt787);
				raw_term rt789;
				rt789.neg = false;
				rt789.extype = raw_term::REL;
				rt789.e.push_back(e699);
				rt789.e.push_back(e1);
				rt789.e.push_back(e248);
				rt789.e.push_back(e249);
				rt789.e.push_back(e59);
				rt789.e.push_back(e47);
				rt789.e.push_back(e3);
				rt789.calc_arity(nullptr);
				sprawformtree ft788 = std::make_shared<raw_form_tree>(elem::NONE, rt789);
				sprawformtree ft785 = std::make_shared<raw_form_tree>(elem::ALT, ft786, ft788);
				raw_rule rr790;
				rr790.h.push_back(rt784);
				rr790.set_prft(ft785);
				elem e791;
				e791.type = elem::SYM;
				e791.e = d.get_lexeme("IS_DICT_CONSISTENT0");
				raw_term rt792;
				rt792.neg = false;
				rt792.extype = raw_term::REL;
				rt792.e.push_back(e791);
				rt792.e.push_back(e1);
				rt792.e.push_back(e233);
				rt792.e.push_back(e234);
				rt792.e.push_back(e233);
				rt792.e.push_back(e234);
				rt792.e.push_back(e3);
				rt792.calc_arity(nullptr);
				elem e796;
				e796.type = elem::SYM;
				e796.e = d.get_lexeme("IS_DICT_CONSISTENT");
				raw_term rt797;
				rt797.neg = false;
				rt797.extype = raw_term::REL;
				rt797.e.push_back(e796);
				rt797.e.push_back(e1);
				rt797.e.push_back(e233);
				rt797.e.push_back(e234);
				rt797.e.push_back(e3);
				rt797.calc_arity(nullptr);
				sprawformtree ft795 = std::make_shared<raw_form_tree>(elem::NONE, rt797);
				elem e800;
				e800.type = elem::SYM;
				e800.e = d.get_lexeme("DICT_CONSISTENT");
				raw_term rt801;
				rt801.neg = false;
				rt801.extype = raw_term::REL;
				rt801.e.push_back(e800);
				rt801.e.push_back(e1);
				rt801.e.push_back(e233);
				rt801.e.push_back(e234);
				rt801.e.push_back(e3);
				rt801.calc_arity(nullptr);
				sprawformtree ft799 = std::make_shared<raw_form_tree>(elem::NONE, rt801);
				sprawformtree ft798 = std::make_shared<raw_form_tree>(elem::NOT, ft799);
				sprawformtree ft794 = std::make_shared<raw_form_tree>(elem::AND, ft795, ft798);
				sprawformtree ft804 = std::make_shared<raw_form_tree>(elem::VAR, e151);
				sprawformtree ft806 = std::make_shared<raw_form_tree>(elem::VAR, e39);
				elem e808;
				e808.type = elem::SYM;
				e808.e = d.get_lexeme("NOT_DICT_CONSISTENT");
				raw_term rt809;
				rt809.neg = false;
				rt809.extype = raw_term::REL;
				rt809.e.push_back(e808);
				rt809.e.push_back(e1);
				rt809.e.push_back(e248);
				rt809.e.push_back(e249);
				rt809.e.push_back(e151);
				rt809.e.push_back(e39);
				rt809.e.push_back(e3);
				rt809.calc_arity(nullptr);
				sprawformtree ft807 = std::make_shared<raw_form_tree>(elem::NONE, rt809);
				sprawformtree ft805 = std::make_shared<raw_form_tree>(elem::EXISTS, ft806, ft807);
				sprawformtree ft803 = std::make_shared<raw_form_tree>(elem::EXISTS, ft804, ft805);
				sprawformtree ft802 = std::make_shared<raw_form_tree>(elem::NOT, ft803);
				sprawformtree ft793 = std::make_shared<raw_form_tree>(elem::AND, ft794, ft802);
				raw_rule rr810;
				rr810.h.push_back(rt792);
				rr810.set_prft(ft793);
				raw_term rt811;
				rt811.neg = false;
				rt811.extype = raw_term::REL;
				rt811.e.push_back(e691);
				rt811.e.push_back(e1);
				rt811.e.push_back(e250);
				rt811.e.push_back(e256);
				rt811.e.push_back(e59);
				rt811.e.push_back(e47);
				rt811.e.push_back(e3);
				rt811.calc_arity(nullptr);
				elem e812;
				e812.type = elem::SYM;
				e812.e = d.get_lexeme("IS_DICT_CONSISTENT1");
				raw_term rt813;
				rt813.neg = false;
				rt813.extype = raw_term::REL;
				rt813.e.push_back(e812);
				rt813.e.push_back(e1);
				rt813.e.push_back(e248);
				rt813.e.push_back(e249);
				rt813.e.push_back(e233);
				rt813.e.push_back(e234);
				rt813.e.push_back(e3);
				rt813.calc_arity(nullptr);
				raw_term rt819;
				rt819.neg = false;
				rt819.extype = raw_term::REL;
				rt819.e.push_back(e791);
				rt819.e.push_back(e1);
				rt819.e.push_back(e248);
				rt819.e.push_back(e249);
				rt819.e.push_back(e233);
				rt819.e.push_back(e234);
				rt819.e.push_back(e3);
				rt819.calc_arity(nullptr);
				sprawformtree ft818 = std::make_shared<raw_form_tree>(elem::NONE, rt819);
				raw_term rt821;
				rt821.neg = false;
				rt821.extype = raw_term::REL;
				rt821.e.push_back(e150);
				rt821.e.push_back(e1);
				rt821.e.push_back(e233);
				rt821.e.push_back(e59);
				rt821.e.push_back(e250);
				rt821.e.push_back(e3);
				rt821.calc_arity(nullptr);
				sprawformtree ft820 = std::make_shared<raw_form_tree>(elem::NONE, rt821);
				sprawformtree ft817 = std::make_shared<raw_form_tree>(elem::AND, ft818, ft820);
				raw_term rt823;
				rt823.neg = false;
				rt823.extype = raw_term::REL;
				rt823.e.push_back(e155);
				rt823.e.push_back(e1);
				rt823.e.push_back(e234);
				rt823.e.push_back(e47);
				rt823.e.push_back(e256);
				rt823.e.push_back(e3);
				rt823.calc_arity(nullptr);
				sprawformtree ft822 = std::make_shared<raw_form_tree>(elem::NONE, rt823);
				sprawformtree ft816 = std::make_shared<raw_form_tree>(elem::AND, ft817, ft822);
				raw_term rt826;
				rt826.neg = false;
				rt826.extype = raw_term::REL;
				rt826.e.push_back(e800);
				rt826.e.push_back(e1);
				rt826.e.push_back(e248);
				rt826.e.push_back(e249);
				rt826.e.push_back(e3);
				rt826.calc_arity(nullptr);
				sprawformtree ft825 = std::make_shared<raw_form_tree>(elem::NONE, rt826);
				sprawformtree ft824 = std::make_shared<raw_form_tree>(elem::NOT, ft825);
				sprawformtree ft815 = std::make_shared<raw_form_tree>(elem::AND, ft816, ft824);
				sprawformtree ft829 = std::make_shared<raw_form_tree>(elem::VAR, e151);
				sprawformtree ft831 = std::make_shared<raw_form_tree>(elem::VAR, e39);
				raw_term rt833;
				rt833.neg = false;
				rt833.extype = raw_term::REL;
				rt833.e.push_back(e808);
				rt833.e.push_back(e1);
				rt833.e.push_back(e248);
				rt833.e.push_back(e249);
				rt833.e.push_back(e151);
				rt833.e.push_back(e39);
				rt833.e.push_back(e3);
				rt833.calc_arity(nullptr);
				sprawformtree ft832 = std::make_shared<raw_form_tree>(elem::NONE, rt833);
				sprawformtree ft830 = std::make_shared<raw_form_tree>(elem::EXISTS, ft831, ft832);
				sprawformtree ft828 = std::make_shared<raw_form_tree>(elem::EXISTS, ft829, ft830);
				sprawformtree ft827 = std::make_shared<raw_form_tree>(elem::NOT, ft828);
				sprawformtree ft814 = std::make_shared<raw_form_tree>(elem::AND, ft815, ft827);
				raw_rule rr834;
				rr834.h.push_back(rt811);
				rr834.h.push_back(rt813);
				rr834.set_prft(ft814);
				raw_term rt835;
				rt835.neg = false;
				rt835.extype = raw_term::REL;
				rt835.e.push_back(e791);
				rt835.e.push_back(e1);
				rt835.e.push_back(e248);
				rt835.e.push_back(e249);
				rt835.e.push_back(e250);
				rt835.e.push_back(e256);
				rt835.e.push_back(e3);
				rt835.calc_arity(nullptr);
				raw_term rt842;
				rt842.neg = false;
				rt842.extype = raw_term::REL;
				rt842.e.push_back(e695);
				rt842.e.push_back(e1);
				rt842.e.push_back(e250);
				rt842.e.push_back(e256);
				rt842.e.push_back(e59);
				rt842.e.push_back(e47);
				rt842.e.push_back(e3);
				rt842.calc_arity(nullptr);
				sprawformtree ft841 = std::make_shared<raw_form_tree>(elem::NONE, rt842);
				raw_term rt844;
				rt844.neg = false;
				rt844.extype = raw_term::REL;
				rt844.e.push_back(e812);
				rt844.e.push_back(e1);
				rt844.e.push_back(e248);
				rt844.e.push_back(e249);
				rt844.e.push_back(e233);
				rt844.e.push_back(e234);
				rt844.e.push_back(e3);
				rt844.calc_arity(nullptr);
				sprawformtree ft843 = std::make_shared<raw_form_tree>(elem::NONE, rt844);
				sprawformtree ft840 = std::make_shared<raw_form_tree>(elem::AND, ft841, ft843);
				raw_term rt846;
				rt846.neg = false;
				rt846.extype = raw_term::REL;
				rt846.e.push_back(e150);
				rt846.e.push_back(e1);
				rt846.e.push_back(e233);
				rt846.e.push_back(e59);
				rt846.e.push_back(e250);
				rt846.e.push_back(e3);
				rt846.calc_arity(nullptr);
				sprawformtree ft845 = std::make_shared<raw_form_tree>(elem::NONE, rt846);
				sprawformtree ft839 = std::make_shared<raw_form_tree>(elem::AND, ft840, ft845);
				raw_term rt848;
				rt848.neg = false;
				rt848.extype = raw_term::REL;
				rt848.e.push_back(e155);
				rt848.e.push_back(e1);
				rt848.e.push_back(e234);
				rt848.e.push_back(e47);
				rt848.e.push_back(e256);
				rt848.e.push_back(e3);
				rt848.calc_arity(nullptr);
				sprawformtree ft847 = std::make_shared<raw_form_tree>(elem::NONE, rt848);
				sprawformtree ft838 = std::make_shared<raw_form_tree>(elem::AND, ft839, ft847);
				raw_term rt851;
				rt851.neg = false;
				rt851.extype = raw_term::REL;
				rt851.e.push_back(e800);
				rt851.e.push_back(e1);
				rt851.e.push_back(e248);
				rt851.e.push_back(e249);
				rt851.e.push_back(e3);
				rt851.calc_arity(nullptr);
				sprawformtree ft850 = std::make_shared<raw_form_tree>(elem::NONE, rt851);
				sprawformtree ft849 = std::make_shared<raw_form_tree>(elem::NOT, ft850);
				sprawformtree ft837 = std::make_shared<raw_form_tree>(elem::AND, ft838, ft849);
				sprawformtree ft854 = std::make_shared<raw_form_tree>(elem::VAR, e151);
				sprawformtree ft856 = std::make_shared<raw_form_tree>(elem::VAR, e39);
				raw_term rt858;
				rt858.neg = false;
				rt858.extype = raw_term::REL;
				rt858.e.push_back(e808);
				rt858.e.push_back(e1);
				rt858.e.push_back(e248);
				rt858.e.push_back(e249);
				rt858.e.push_back(e151);
				rt858.e.push_back(e39);
				rt858.e.push_back(e3);
				rt858.calc_arity(nullptr);
				sprawformtree ft857 = std::make_shared<raw_form_tree>(elem::NONE, rt858);
				sprawformtree ft855 = std::make_shared<raw_form_tree>(elem::EXISTS, ft856, ft857);
				sprawformtree ft853 = std::make_shared<raw_form_tree>(elem::EXISTS, ft854, ft855);
				sprawformtree ft852 = std::make_shared<raw_form_tree>(elem::NOT, ft853);
				sprawformtree ft836 = std::make_shared<raw_form_tree>(elem::AND, ft837, ft852);
				raw_rule rr859;
				rr859.h.push_back(rt835);
				rr859.set_prft(ft836);
				raw_term rt860;
				rt860.neg = false;
				rt860.extype = raw_term::REL;
				rt860.e.push_back(e808);
				rt860.e.push_back(e1);
				rt860.e.push_back(e248);
				rt860.e.push_back(e249);
				rt860.e.push_back(e250);
				rt860.e.push_back(e256);
				rt860.e.push_back(e3);
				rt860.calc_arity(nullptr);
				raw_term rt867;
				rt867.neg = false;
				rt867.extype = raw_term::REL;
				rt867.e.push_back(e699);
				rt867.e.push_back(e1);
				rt867.e.push_back(e250);
				rt867.e.push_back(e256);
				rt867.e.push_back(e59);
				rt867.e.push_back(e47);
				rt867.e.push_back(e3);
				rt867.calc_arity(nullptr);
				sprawformtree ft866 = std::make_shared<raw_form_tree>(elem::NONE, rt867);
				raw_term rt869;
				rt869.neg = false;
				rt869.extype = raw_term::REL;
				rt869.e.push_back(e812);
				rt869.e.push_back(e1);
				rt869.e.push_back(e248);
				rt869.e.push_back(e249);
				rt869.e.push_back(e233);
				rt869.e.push_back(e234);
				rt869.e.push_back(e3);
				rt869.calc_arity(nullptr);
				sprawformtree ft868 = std::make_shared<raw_form_tree>(elem::NONE, rt869);
				sprawformtree ft865 = std::make_shared<raw_form_tree>(elem::AND, ft866, ft868);
				raw_term rt871;
				rt871.neg = false;
				rt871.extype = raw_term::REL;
				rt871.e.push_back(e150);
				rt871.e.push_back(e1);
				rt871.e.push_back(e233);
				rt871.e.push_back(e59);
				rt871.e.push_back(e250);
				rt871.e.push_back(e3);
				rt871.calc_arity(nullptr);
				sprawformtree ft870 = std::make_shared<raw_form_tree>(elem::NONE, rt871);
				sprawformtree ft864 = std::make_shared<raw_form_tree>(elem::AND, ft865, ft870);
				raw_term rt873;
				rt873.neg = false;
				rt873.extype = raw_term::REL;
				rt873.e.push_back(e155);
				rt873.e.push_back(e1);
				rt873.e.push_back(e234);
				rt873.e.push_back(e47);
				rt873.e.push_back(e256);
				rt873.e.push_back(e3);
				rt873.calc_arity(nullptr);
				sprawformtree ft872 = std::make_shared<raw_form_tree>(elem::NONE, rt873);
				sprawformtree ft863 = std::make_shared<raw_form_tree>(elem::AND, ft864, ft872);
				raw_term rt876;
				rt876.neg = false;
				rt876.extype = raw_term::REL;
				rt876.e.push_back(e800);
				rt876.e.push_back(e1);
				rt876.e.push_back(e248);
				rt876.e.push_back(e249);
				rt876.e.push_back(e3);
				rt876.calc_arity(nullptr);
				sprawformtree ft875 = std::make_shared<raw_form_tree>(elem::NONE, rt876);
				sprawformtree ft874 = std::make_shared<raw_form_tree>(elem::NOT, ft875);
				sprawformtree ft862 = std::make_shared<raw_form_tree>(elem::AND, ft863, ft874);
				sprawformtree ft879 = std::make_shared<raw_form_tree>(elem::VAR, e151);
				sprawformtree ft881 = std::make_shared<raw_form_tree>(elem::VAR, e39);
				raw_term rt883;
				rt883.neg = false;
				rt883.extype = raw_term::REL;
				rt883.e.push_back(e808);
				rt883.e.push_back(e1);
				rt883.e.push_back(e248);
				rt883.e.push_back(e249);
				rt883.e.push_back(e151);
				rt883.e.push_back(e39);
				rt883.e.push_back(e3);
				rt883.calc_arity(nullptr);
				sprawformtree ft882 = std::make_shared<raw_form_tree>(elem::NONE, rt883);
				sprawformtree ft880 = std::make_shared<raw_form_tree>(elem::EXISTS, ft881, ft882);
				sprawformtree ft878 = std::make_shared<raw_form_tree>(elem::EXISTS, ft879, ft880);
				sprawformtree ft877 = std::make_shared<raw_form_tree>(elem::NOT, ft878);
				sprawformtree ft861 = std::make_shared<raw_form_tree>(elem::AND, ft862, ft877);
				raw_rule rr884;
				rr884.h.push_back(rt860);
				rr884.set_prft(ft861);
				raw_term rt885;
				rt885.neg = false;
				rt885.extype = raw_term::REL;
				rt885.e.push_back(e800);
				rt885.e.push_back(e1);
				rt885.e.push_back(e248);
				rt885.e.push_back(e249);
				rt885.e.push_back(e3);
				rt885.calc_arity(nullptr);
				raw_term rt891;
				rt891.neg = false;
				rt891.extype = raw_term::REL;
				rt891.e.push_back(e791);
				rt891.e.push_back(e1);
				rt891.e.push_back(e248);
				rt891.e.push_back(e249);
				rt891.e.push_back(e233);
				rt891.e.push_back(e234);
				rt891.e.push_back(e3);
				rt891.calc_arity(nullptr);
				sprawformtree ft890 = std::make_shared<raw_form_tree>(elem::NONE, rt891);
				raw_term rt893;
				rt893.neg = false;
				rt893.extype = raw_term::REL;
				rt893.e.push_back(e150);
				rt893.e.push_back(e1);
				rt893.e.push_back(e233);
				rt893.e.push_back(e3);
				rt893.calc_arity(nullptr);
				sprawformtree ft892 = std::make_shared<raw_form_tree>(elem::NONE, rt893);
				sprawformtree ft889 = std::make_shared<raw_form_tree>(elem::AND, ft890, ft892);
				raw_term rt895;
				rt895.neg = false;
				rt895.extype = raw_term::REL;
				rt895.e.push_back(e155);
				rt895.e.push_back(e1);
				rt895.e.push_back(e234);
				rt895.e.push_back(e3);
				rt895.calc_arity(nullptr);
				sprawformtree ft894 = std::make_shared<raw_form_tree>(elem::NONE, rt895);
				sprawformtree ft888 = std::make_shared<raw_form_tree>(elem::AND, ft889, ft894);
				raw_term rt898;
				rt898.neg = false;
				rt898.extype = raw_term::REL;
				rt898.e.push_back(e800);
				rt898.e.push_back(e1);
				rt898.e.push_back(e248);
				rt898.e.push_back(e249);
				rt898.e.push_back(e3);
				rt898.calc_arity(nullptr);
				sprawformtree ft897 = std::make_shared<raw_form_tree>(elem::NONE, rt898);
				sprawformtree ft896 = std::make_shared<raw_form_tree>(elem::NOT, ft897);
				sprawformtree ft887 = std::make_shared<raw_form_tree>(elem::AND, ft888, ft896);
				sprawformtree ft901 = std::make_shared<raw_form_tree>(elem::VAR, e151);
				sprawformtree ft903 = std::make_shared<raw_form_tree>(elem::VAR, e39);
				raw_term rt905;
				rt905.neg = false;
				rt905.extype = raw_term::REL;
				rt905.e.push_back(e808);
				rt905.e.push_back(e1);
				rt905.e.push_back(e248);
				rt905.e.push_back(e249);
				rt905.e.push_back(e151);
				rt905.e.push_back(e39);
				rt905.e.push_back(e3);
				rt905.calc_arity(nullptr);
				sprawformtree ft904 = std::make_shared<raw_form_tree>(elem::NONE, rt905);
				sprawformtree ft902 = std::make_shared<raw_form_tree>(elem::EXISTS, ft903, ft904);
				sprawformtree ft900 = std::make_shared<raw_form_tree>(elem::EXISTS, ft901, ft902);
				sprawformtree ft899 = std::make_shared<raw_form_tree>(elem::NOT, ft900);
				sprawformtree ft886 = std::make_shared<raw_form_tree>(elem::AND, ft887, ft899);
				raw_rule rr906;
				rr906.h.push_back(rt885);
				rr906.set_prft(ft886);
				raw_term rt907;
				rt907.neg = true;
				rt907.extype = raw_term::REL;
				rt907.e.push_back(e791);
				rt907.e.push_back(e1);
				rt907.e.push_back(e248);
				rt907.e.push_back(e249);
				rt907.e.push_back(e233);
				rt907.e.push_back(e234);
				rt907.e.push_back(e3);
				rt907.calc_arity(nullptr);
				raw_term rt908;
				rt908.neg = true;
				rt908.extype = raw_term::REL;
				rt908.e.push_back(e812);
				rt908.e.push_back(e1);
				rt908.e.push_back(e248);
				rt908.e.push_back(e249);
				rt908.e.push_back(e233);
				rt908.e.push_back(e234);
				rt908.e.push_back(e3);
				rt908.calc_arity(nullptr);
				raw_term rt911;
				rt911.neg = false;
				rt911.extype = raw_term::REL;
				rt911.e.push_back(e800);
				rt911.e.push_back(e1);
				rt911.e.push_back(e248);
				rt911.e.push_back(e249);
				rt911.e.push_back(e3);
				rt911.calc_arity(nullptr);
				sprawformtree ft910 = std::make_shared<raw_form_tree>(elem::NONE, rt911);
				elem e913;
				e913.type = elem::VAR;
				e913.e = d.get_lexeme("?axs");
				elem e914;
				e914.type = elem::VAR;
				e914.e = d.get_lexeme("?ays");
				raw_term rt915;
				rt915.neg = false;
				rt915.extype = raw_term::REL;
				rt915.e.push_back(e808);
				rt915.e.push_back(e1);
				rt915.e.push_back(e248);
				rt915.e.push_back(e249);
				rt915.e.push_back(e913);
				rt915.e.push_back(e914);
				rt915.e.push_back(e3);
				rt915.calc_arity(nullptr);
				sprawformtree ft912 = std::make_shared<raw_form_tree>(elem::NONE, rt915);
				sprawformtree ft909 = std::make_shared<raw_form_tree>(elem::ALT, ft910, ft912);
				raw_rule rr916;
				rr916.h.push_back(rt907);
				rr916.h.push_back(rt908);
				rr916.set_prft(ft909);
				elem e917;
				e917.type = elem::SYM;
				e917.e = d.get_lexeme("DO_FIX_SYMS0");
				raw_term rt918;
				rt918.neg = false;
				rt918.extype = raw_term::REL;
				rt918.e.push_back(e917);
				rt918.e.push_back(e1);
				rt918.e.push_back(e274);
				rt918.e.push_back(e274);
				rt918.e.push_back(e335);
				rt918.e.push_back(e3);
				rt918.calc_arity(nullptr);
				elem e922;
				e922.type = elem::SYM;
				e922.e = d.get_lexeme("DO_FIX_SYMS");
				raw_term rt923;
				rt923.neg = false;
				rt923.extype = raw_term::REL;
				rt923.e.push_back(e922);
				rt923.e.push_back(e1);
				rt923.e.push_back(e274);
				rt923.e.push_back(e3);
				rt923.calc_arity(nullptr);
				sprawformtree ft921 = std::make_shared<raw_form_tree>(elem::NONE, rt923);
				raw_term rt925;
				rt925.neg = false;
				rt925.extype = raw_term::REL;
				rt925.e.push_back(e155);
				rt925.e.push_back(e1);
				rt925.e.push_back(e335);
				rt925.e.push_back(e3);
				rt925.calc_arity(nullptr);
				sprawformtree ft924 = std::make_shared<raw_form_tree>(elem::NONE, rt925);
				sprawformtree ft920 = std::make_shared<raw_form_tree>(elem::AND, ft921, ft924);
				sprawformtree ft928 = std::make_shared<raw_form_tree>(elem::VAR, e151);
				elem e930;
				e930.type = elem::SYM;
				e930.e = d.get_lexeme("FIX_SYMS");
				raw_term rt931;
				rt931.neg = false;
				rt931.extype = raw_term::REL;
				rt931.e.push_back(e930);
				rt931.e.push_back(e1);
				rt931.e.push_back(e274);
				rt931.e.push_back(e151);
				rt931.e.push_back(e3);
				rt931.calc_arity(nullptr);
				sprawformtree ft929 = std::make_shared<raw_form_tree>(elem::NONE, rt931);
				sprawformtree ft927 = std::make_shared<raw_form_tree>(elem::EXISTS, ft928, ft929);
				sprawformtree ft926 = std::make_shared<raw_form_tree>(elem::NOT, ft927);
				sprawformtree ft919 = std::make_shared<raw_form_tree>(elem::AND, ft920, ft926);
				raw_rule rr932;
				rr932.h.push_back(rt918);
				rr932.set_prft(ft919);
				elem e933;
				e933.type = elem::VAR;
				e933.e = d.get_lexeme("?oas");
				raw_term rt934;
				rt934.neg = false;
				rt934.extype = raw_term::REL;
				rt934.e.push_back(e917);
				rt934.e.push_back(e1);
				rt934.e.push_back(e933);
				rt934.e.push_back(e357);
				rt934.e.push_back(e335);
				rt934.e.push_back(e3);
				rt934.calc_arity(nullptr);
				elem e940;
				e940.type = elem::VAR;
				e940.e = d.get_lexeme("?bs_tl");
				raw_term rt941;
				rt941.neg = false;
				rt941.extype = raw_term::REL;
				rt941.e.push_back(e917);
				rt941.e.push_back(e1);
				rt941.e.push_back(e933);
				rt941.e.push_back(e274);
				rt941.e.push_back(e940);
				rt941.e.push_back(e3);
				rt941.calc_arity(nullptr);
				sprawformtree ft939 = std::make_shared<raw_form_tree>(elem::NONE, rt941);
				raw_term rt943;
				rt943.neg = false;
				rt943.extype = raw_term::REL;
				rt943.e.push_back(e150);
				rt943.e.push_back(e1);
				rt943.e.push_back(e274);
				rt943.e.push_back(e356);
				rt943.e.push_back(e357);
				rt943.e.push_back(e3);
				rt943.calc_arity(nullptr);
				sprawformtree ft942 = std::make_shared<raw_form_tree>(elem::NONE, rt943);
				sprawformtree ft938 = std::make_shared<raw_form_tree>(elem::AND, ft939, ft942);
				elem e947;
				e947.type = elem::SYM;
				e947.e = d.get_lexeme("VARS");
				raw_term rt948;
				rt948.neg = false;
				rt948.extype = raw_term::REL;
				rt948.e.push_back(e6);
				rt948.e.push_back(e1);
				rt948.e.push_back(e947);
				rt948.e.push_back(e356);
				rt948.e.push_back(e3);
				rt948.calc_arity(nullptr);
				sprawformtree ft946 = std::make_shared<raw_form_tree>(elem::NONE, rt948);
				elem e950;
				e950.type = elem::VAR;
				e950.e = d.get_lexeme("?bs_hd");
				raw_term rt951;
				rt951.neg = false;
				rt951.extype = raw_term::REL;
				rt951.e.push_back(e158);
				rt951.e.push_back(e1);
				rt951.e.push_back(e950);
				rt951.e.push_back(e3);
				rt951.calc_arity(nullptr);
				sprawformtree ft949 = std::make_shared<raw_form_tree>(elem::NONE, rt951);
				sprawformtree ft945 = std::make_shared<raw_form_tree>(elem::AND, ft946, ft949);
				elem e954;
				e954.type = elem::SYM;
				e954.e = d.get_lexeme("SYM");
				raw_term rt955;
				rt955.neg = false;
				rt955.extype = raw_term::REL;
				rt955.e.push_back(e6);
				rt955.e.push_back(e1);
				rt955.e.push_back(e954);
				rt955.e.push_back(e356);
				rt955.e.push_back(e3);
				rt955.calc_arity(nullptr);
				sprawformtree ft953 = std::make_shared<raw_form_tree>(elem::NONE, rt955);
				raw_term rt957;
				rt957.neg = false;
				rt957.extype = raw_term::EQ;
				rt957.e.push_back(e356);
				rt957.e.push_back(e109);
				rt957.e.push_back(e950);
				rt957.calc_arity(nullptr);
				sprawformtree ft956 = std::make_shared<raw_form_tree>(elem::NONE, rt957);
				sprawformtree ft952 = std::make_shared<raw_form_tree>(elem::AND, ft953, ft956);
				sprawformtree ft944 = std::make_shared<raw_form_tree>(elem::ALT, ft945, ft952);
				sprawformtree ft937 = std::make_shared<raw_form_tree>(elem::AND, ft938, ft944);
				raw_term rt959;
				rt959.neg = false;
				rt959.extype = raw_term::REL;
				rt959.e.push_back(e155);
				rt959.e.push_back(e1);
				rt959.e.push_back(e335);
				rt959.e.push_back(e950);
				rt959.e.push_back(e940);
				rt959.e.push_back(e3);
				rt959.calc_arity(nullptr);
				sprawformtree ft958 = std::make_shared<raw_form_tree>(elem::NONE, rt959);
				sprawformtree ft936 = std::make_shared<raw_form_tree>(elem::AND, ft937, ft958);
				sprawformtree ft962 = std::make_shared<raw_form_tree>(elem::VAR, e151);
				raw_term rt964;
				rt964.neg = false;
				rt964.extype = raw_term::REL;
				rt964.e.push_back(e930);
				rt964.e.push_back(e1);
				rt964.e.push_back(e933);
				rt964.e.push_back(e151);
				rt964.e.push_back(e3);
				rt964.calc_arity(nullptr);
				sprawformtree ft963 = std::make_shared<raw_form_tree>(elem::NONE, rt964);
				sprawformtree ft961 = std::make_shared<raw_form_tree>(elem::EXISTS, ft962, ft963);
				sprawformtree ft960 = std::make_shared<raw_form_tree>(elem::NOT, ft961);
				sprawformtree ft935 = std::make_shared<raw_form_tree>(elem::AND, ft936, ft960);
				raw_rule rr965;
				rr965.h.push_back(rt934);
				rr965.set_prft(ft935);
				raw_term rt966;
				rt966.neg = false;
				rt966.extype = raw_term::REL;
				rt966.e.push_back(e334);
				rt966.e.push_back(e1);
				rt966.e.push_back(e335);
				rt966.e.push_back(e3);
				rt966.calc_arity(nullptr);
				elem e967;
				e967.type = elem::SYM;
				e967.e = d.get_lexeme("DO_FIX_SYMS1");
				raw_term rt968;
				rt968.neg = false;
				rt968.extype = raw_term::REL;
				rt968.e.push_back(e967);
				rt968.e.push_back(e1);
				rt968.e.push_back(e933);
				rt968.e.push_back(e335);
				rt968.e.push_back(e3);
				rt968.calc_arity(nullptr);
				raw_term rt972;
				rt972.neg = false;
				rt972.extype = raw_term::REL;
				rt972.e.push_back(e917);
				rt972.e.push_back(e1);
				rt972.e.push_back(e933);
				rt972.e.push_back(e274);
				rt972.e.push_back(e335);
				rt972.e.push_back(e3);
				rt972.calc_arity(nullptr);
				sprawformtree ft971 = std::make_shared<raw_form_tree>(elem::NONE, rt972);
				raw_term rt974;
				rt974.neg = false;
				rt974.extype = raw_term::REL;
				rt974.e.push_back(e150);
				rt974.e.push_back(e1);
				rt974.e.push_back(e274);
				rt974.e.push_back(e3);
				rt974.calc_arity(nullptr);
				sprawformtree ft973 = std::make_shared<raw_form_tree>(elem::NONE, rt974);
				sprawformtree ft970 = std::make_shared<raw_form_tree>(elem::AND, ft971, ft973);
				sprawformtree ft977 = std::make_shared<raw_form_tree>(elem::VAR, e151);
				raw_term rt979;
				rt979.neg = false;
				rt979.extype = raw_term::REL;
				rt979.e.push_back(e930);
				rt979.e.push_back(e1);
				rt979.e.push_back(e933);
				rt979.e.push_back(e151);
				rt979.e.push_back(e3);
				rt979.calc_arity(nullptr);
				sprawformtree ft978 = std::make_shared<raw_form_tree>(elem::NONE, rt979);
				sprawformtree ft976 = std::make_shared<raw_form_tree>(elem::EXISTS, ft977, ft978);
				sprawformtree ft975 = std::make_shared<raw_form_tree>(elem::NOT, ft976);
				sprawformtree ft969 = std::make_shared<raw_form_tree>(elem::AND, ft970, ft975);
				raw_rule rr980;
				rr980.h.push_back(rt966);
				rr980.h.push_back(rt968);
				rr980.set_prft(ft969);
				raw_term rt981;
				rt981.neg = false;
				rt981.extype = raw_term::REL;
				rt981.e.push_back(e930);
				rt981.e.push_back(e1);
				rt981.e.push_back(e274);
				rt981.e.push_back(e335);
				rt981.e.push_back(e3);
				rt981.calc_arity(nullptr);
				raw_term rt984;
				rt984.neg = false;
				rt984.extype = raw_term::REL;
				rt984.e.push_back(e967);
				rt984.e.push_back(e1);
				rt984.e.push_back(e274);
				rt984.e.push_back(e243);
				rt984.e.push_back(e3);
				rt984.calc_arity(nullptr);
				sprawformtree ft983 = std::make_shared<raw_form_tree>(elem::NONE, rt984);
				raw_term rt986;
				rt986.neg = false;
				rt986.extype = raw_term::REL;
				rt986.e.push_back(e347);
				rt986.e.push_back(e1);
				rt986.e.push_back(e243);
				rt986.e.push_back(e335);
				rt986.e.push_back(e3);
				rt986.calc_arity(nullptr);
				sprawformtree ft985 = std::make_shared<raw_form_tree>(elem::NONE, rt986);
				sprawformtree ft982 = std::make_shared<raw_form_tree>(elem::AND, ft983, ft985);
				raw_rule rr987;
				rr987.h.push_back(rt981);
				rr987.set_prft(ft982);
				raw_term rt988;
				rt988.neg = true;
				rt988.extype = raw_term::REL;
				rt988.e.push_back(e917);
				rt988.e.push_back(e1);
				rt988.e.push_back(e933);
				rt988.e.push_back(e274);
				rt988.e.push_back(e335);
				rt988.e.push_back(e3);
				rt988.calc_arity(nullptr);
				raw_term rt989;
				rt989.neg = true;
				rt989.extype = raw_term::REL;
				rt989.e.push_back(e967);
				rt989.e.push_back(e1);
				rt989.e.push_back(e933);
				rt989.e.push_back(e335);
				rt989.e.push_back(e3);
				rt989.calc_arity(nullptr);
				raw_term rt991;
				rt991.neg = false;
				rt991.extype = raw_term::REL;
				rt991.e.push_back(e930);
				rt991.e.push_back(e1);
				rt991.e.push_back(e933);
				rt991.e.push_back(e151);
				rt991.e.push_back(e3);
				rt991.calc_arity(nullptr);
				sprawformtree ft990 = std::make_shared<raw_form_tree>(elem::NONE, rt991);
				raw_rule rr992;
				rr992.h.push_back(rt988);
				rr992.h.push_back(rt989);
				rr992.set_prft(ft990);
				raw_term rt993;
				rt993.neg = false;
				rt993.extype = raw_term::REL;
				rt993.e.push_back(e46);
				rt993.e.push_back(e1);
				rt993.e.push_back(e2);
				rt993.e.push_back(e3);
				rt993.calc_arity(nullptr);
				elem e999;
				e999.type = elem::VAR;
				e999.e = d.get_lexeme("?e0");
				elem e1000;
				e1000.type = elem::VAR;
				e1000.e = d.get_lexeme("?e1");
				raw_term rt1001;
				rt1001.neg = false;
				rt1001.extype = raw_term::REL;
				rt1001.e.push_back(e6);
				rt1001.e.push_back(e1);
				rt1001.e.push_back(e37);
				rt1001.e.push_back(e2);
				rt1001.e.push_back(e999);
				rt1001.e.push_back(e1000);
				rt1001.e.push_back(e3);
				rt1001.calc_arity(nullptr);
				sprawformtree ft998 = std::make_shared<raw_form_tree>(elem::NONE, rt1001);
				elem e1003;
				e1003.type = elem::VAR;
				e1003.e = d.get_lexeme("?nm");
				raw_term rt1004;
				rt1004.neg = false;
				rt1004.extype = raw_term::REL;
				rt1004.e.push_back(e6);
				rt1004.e.push_back(e1);
				rt1004.e.push_back(e7);
				rt1004.e.push_back(e999);
				rt1004.e.push_back(e1003);
				rt1004.e.push_back(e243);
				rt1004.e.push_back(e3);
				rt1004.calc_arity(nullptr);
				sprawformtree ft1002 = std::make_shared<raw_form_tree>(elem::NONE, rt1004);
				sprawformtree ft997 = std::make_shared<raw_form_tree>(elem::AND, ft998, ft1002);
				sprawformtree ft1007 = std::make_shared<raw_form_tree>(elem::VAR, e274);
				sprawformtree ft1009 = std::make_shared<raw_form_tree>(elem::VAR, e335);
				elem e1011;
				e1011.type = elem::SYM;
				e1011.e = d.get_lexeme("FORMULA_OUT");
				raw_term rt1012;
				rt1012.neg = false;
				rt1012.extype = raw_term::REL;
				rt1012.e.push_back(e1011);
				rt1012.e.push_back(e1);
				rt1012.e.push_back(e1000);
				rt1012.e.push_back(e274);
				rt1012.e.push_back(e335);
				rt1012.e.push_back(e3);
				rt1012.calc_arity(nullptr);
				sprawformtree ft1010 = std::make_shared<raw_form_tree>(elem::NONE, rt1012);
				sprawformtree ft1008 = std::make_shared<raw_form_tree>(elem::EXISTS, ft1009, ft1010);
				sprawformtree ft1006 = std::make_shared<raw_form_tree>(elem::EXISTS, ft1007, ft1008);
				sprawformtree ft1005 = std::make_shared<raw_form_tree>(elem::NOT, ft1006);
				sprawformtree ft996 = std::make_shared<raw_form_tree>(elem::AND, ft997, ft1005);
				raw_term rt1014;
				rt1014.neg = false;
				rt1014.extype = raw_term::REL;
				rt1014.e.push_back(e42);
				rt1014.e.push_back(e1);
				rt1014.e.push_back(e3);
				rt1014.calc_arity(nullptr);
				sprawformtree ft1013 = std::make_shared<raw_form_tree>(elem::NONE, rt1014);
				sprawformtree ft995 = std::make_shared<raw_form_tree>(elem::AND, ft996, ft1013);
				raw_term rt1017;
				rt1017.neg = false;
				rt1017.extype = raw_term::REL;
				rt1017.e.push_back(e70);
				rt1017.e.push_back(e1);
				rt1017.e.push_back(e3);
				rt1017.calc_arity(nullptr);
				sprawformtree ft1016 = std::make_shared<raw_form_tree>(elem::NONE, rt1017);
				sprawformtree ft1015 = std::make_shared<raw_form_tree>(elem::NOT, ft1016);
				sprawformtree ft994 = std::make_shared<raw_form_tree>(elem::AND, ft995, ft1015);
				raw_rule rr1018;
				rr1018.h.push_back(rt993);
				rr1018.set_prft(ft994);
				raw_term rt1019;
				rt1019.neg = false;
				rt1019.extype = raw_term::REL;
				rt1019.e.push_back(e600);
				rt1019.e.push_back(e1);
				rt1019.e.push_back(e274);
				rt1019.e.push_back(e335);
				rt1019.e.push_back(e243);
				rt1019.e.push_back(e3);
				rt1019.calc_arity(nullptr);
				raw_term rt1020;
				rt1020.neg = false;
				rt1020.extype = raw_term::REL;
				rt1020.e.push_back(e796);
				rt1020.e.push_back(e1);
				rt1020.e.push_back(e274);
				rt1020.e.push_back(e335);
				rt1020.e.push_back(e3);
				rt1020.calc_arity(nullptr);
				raw_term rt1021;
				rt1021.neg = false;
				rt1021.extype = raw_term::REL;
				rt1021.e.push_back(e922);
				rt1021.e.push_back(e1);
				rt1021.e.push_back(e243);
				rt1021.e.push_back(e3);
				rt1021.calc_arity(nullptr);
				raw_term rt1027;
				rt1027.neg = false;
				rt1027.extype = raw_term::REL;
				rt1027.e.push_back(e6);
				rt1027.e.push_back(e1);
				rt1027.e.push_back(e37);
				rt1027.e.push_back(e2);
				rt1027.e.push_back(e999);
				rt1027.e.push_back(e1000);
				rt1027.e.push_back(e3);
				rt1027.calc_arity(nullptr);
				sprawformtree ft1026 = std::make_shared<raw_form_tree>(elem::NONE, rt1027);
				raw_term rt1029;
				rt1029.neg = false;
				rt1029.extype = raw_term::REL;
				rt1029.e.push_back(e6);
				rt1029.e.push_back(e1);
				rt1029.e.push_back(e7);
				rt1029.e.push_back(e999);
				rt1029.e.push_back(e1003);
				rt1029.e.push_back(e243);
				rt1029.e.push_back(e3);
				rt1029.calc_arity(nullptr);
				sprawformtree ft1028 = std::make_shared<raw_form_tree>(elem::NONE, rt1029);
				sprawformtree ft1025 = std::make_shared<raw_form_tree>(elem::AND, ft1026, ft1028);
				raw_term rt1031;
				rt1031.neg = false;
				rt1031.extype = raw_term::REL;
				rt1031.e.push_back(e1011);
				rt1031.e.push_back(e1);
				rt1031.e.push_back(e1000);
				rt1031.e.push_back(e274);
				rt1031.e.push_back(e335);
				rt1031.e.push_back(e3);
				rt1031.calc_arity(nullptr);
				sprawformtree ft1030 = std::make_shared<raw_form_tree>(elem::NONE, rt1031);
				sprawformtree ft1024 = std::make_shared<raw_form_tree>(elem::AND, ft1025, ft1030);
				raw_term rt1033;
				rt1033.neg = false;
				rt1033.extype = raw_term::REL;
				rt1033.e.push_back(e42);
				rt1033.e.push_back(e1);
				rt1033.e.push_back(e3);
				rt1033.calc_arity(nullptr);
				sprawformtree ft1032 = std::make_shared<raw_form_tree>(elem::NONE, rt1033);
				sprawformtree ft1023 = std::make_shared<raw_form_tree>(elem::AND, ft1024, ft1032);
				raw_term rt1036;
				rt1036.neg = false;
				rt1036.extype = raw_term::REL;
				rt1036.e.push_back(e70);
				rt1036.e.push_back(e1);
				rt1036.e.push_back(e3);
				rt1036.calc_arity(nullptr);
				sprawformtree ft1035 = std::make_shared<raw_form_tree>(elem::NONE, rt1036);
				sprawformtree ft1034 = std::make_shared<raw_form_tree>(elem::NOT, ft1035);
				sprawformtree ft1022 = std::make_shared<raw_form_tree>(elem::AND, ft1023, ft1034);
				raw_rule rr1037;
				rr1037.h.push_back(rt1019);
				rr1037.h.push_back(rt1020);
				rr1037.h.push_back(rt1021);
				rr1037.set_prft(ft1022);
				raw_term rt1038;
				rt1038.neg = false;
				rt1038.extype = raw_term::REL;
				rt1038.e.push_back(e46);
				rt1038.e.push_back(e1);
				rt1038.e.push_back(e2);
				rt1038.e.push_back(e3);
				rt1038.calc_arity(nullptr);
				raw_term rt1046;
				rt1046.neg = false;
				rt1046.extype = raw_term::REL;
				rt1046.e.push_back(e6);
				rt1046.e.push_back(e1);
				rt1046.e.push_back(e37);
				rt1046.e.push_back(e2);
				rt1046.e.push_back(e999);
				rt1046.e.push_back(e1000);
				rt1046.e.push_back(e3);
				rt1046.calc_arity(nullptr);
				sprawformtree ft1045 = std::make_shared<raw_form_tree>(elem::NONE, rt1046);
				raw_term rt1048;
				rt1048.neg = false;
				rt1048.extype = raw_term::REL;
				rt1048.e.push_back(e6);
				rt1048.e.push_back(e1);
				rt1048.e.push_back(e7);
				rt1048.e.push_back(e999);
				rt1048.e.push_back(e1003);
				rt1048.e.push_back(e243);
				rt1048.e.push_back(e3);
				rt1048.calc_arity(nullptr);
				sprawformtree ft1047 = std::make_shared<raw_form_tree>(elem::NONE, rt1048);
				sprawformtree ft1044 = std::make_shared<raw_form_tree>(elem::AND, ft1045, ft1047);
				raw_term rt1050;
				rt1050.neg = false;
				rt1050.extype = raw_term::REL;
				rt1050.e.push_back(e1011);
				rt1050.e.push_back(e1);
				rt1050.e.push_back(e1000);
				rt1050.e.push_back(e274);
				rt1050.e.push_back(e335);
				rt1050.e.push_back(e3);
				rt1050.calc_arity(nullptr);
				sprawformtree ft1049 = std::make_shared<raw_form_tree>(elem::NONE, rt1050);
				sprawformtree ft1043 = std::make_shared<raw_form_tree>(elem::AND, ft1044, ft1049);
				elem e1052;
				e1052.type = elem::VAR;
				e1052.e = d.get_lexeme("?ds1");
				raw_term rt1053;
				rt1053.neg = false;
				rt1053.extype = raw_term::REL;
				rt1053.e.push_back(e600);
				rt1053.e.push_back(e1);
				rt1053.e.push_back(e274);
				rt1053.e.push_back(e335);
				rt1053.e.push_back(e243);
				rt1053.e.push_back(e1052);
				rt1053.e.push_back(e3);
				rt1053.calc_arity(nullptr);
				sprawformtree ft1051 = std::make_shared<raw_form_tree>(elem::NONE, rt1053);
				sprawformtree ft1042 = std::make_shared<raw_form_tree>(elem::AND, ft1043, ft1051);
				elem e1055;
				e1055.type = elem::VAR;
				e1055.e = d.get_lexeme("?ds2");
				raw_term rt1056;
				rt1056.neg = false;
				rt1056.extype = raw_term::REL;
				rt1056.e.push_back(e930);
				rt1056.e.push_back(e1);
				rt1056.e.push_back(e243);
				rt1056.e.push_back(e1055);
				rt1056.e.push_back(e3);
				rt1056.calc_arity(nullptr);
				sprawformtree ft1054 = std::make_shared<raw_form_tree>(elem::NONE, rt1056);
				sprawformtree ft1041 = std::make_shared<raw_form_tree>(elem::AND, ft1042, ft1054);
				raw_term rt1059;
				rt1059.neg = false;
				rt1059.extype = raw_term::REL;
				rt1059.e.push_back(e800);
				rt1059.e.push_back(e1);
				rt1059.e.push_back(e274);
				rt1059.e.push_back(e335);
				rt1059.e.push_back(e3);
				rt1059.calc_arity(nullptr);
				sprawformtree ft1058 = std::make_shared<raw_form_tree>(elem::NONE, rt1059);
				raw_term rt1061;
				rt1061.neg = false;
				rt1061.extype = raw_term::REL;
				rt1061.e.push_back(e808);
				rt1061.e.push_back(e1);
				rt1061.e.push_back(e274);
				rt1061.e.push_back(e335);
				rt1061.e.push_back(e3);
				rt1061.calc_arity(nullptr);
				sprawformtree ft1060 = std::make_shared<raw_form_tree>(elem::NONE, rt1061);
				sprawformtree ft1057 = std::make_shared<raw_form_tree>(elem::ALT, ft1058, ft1060);
				sprawformtree ft1040 = std::make_shared<raw_form_tree>(elem::AND, ft1041, ft1057);
				raw_term rt1063;
				rt1063.neg = false;
				rt1063.extype = raw_term::REL;
				rt1063.e.push_back(e42);
				rt1063.e.push_back(e1);
				rt1063.e.push_back(e3);
				rt1063.calc_arity(nullptr);
				sprawformtree ft1062 = std::make_shared<raw_form_tree>(elem::NONE, rt1063);
				sprawformtree ft1039 = std::make_shared<raw_form_tree>(elem::AND, ft1040, ft1062);
				raw_rule rr1064;
				rr1064.h.push_back(rt1038);
				rr1064.set_prft(ft1039);
				elem &e1065 = out_rel;
				elem e1066;
				e1066.type = elem::VAR;
				e1066.e = d.get_lexeme("?ds");
				raw_term rt1067;
				rt1067.neg = false;
				rt1067.extype = raw_term::REL;
				rt1067.e.push_back(e1065);
				rt1067.e.push_back(e1);
				rt1067.e.push_back(e1003);
				rt1067.e.push_back(e1066);
				rt1067.e.push_back(e3);
				rt1067.calc_arity(nullptr);
				raw_term rt1075;
				rt1075.neg = false;
				rt1075.extype = raw_term::REL;
				rt1075.e.push_back(e6);
				rt1075.e.push_back(e1);
				rt1075.e.push_back(e37);
				rt1075.e.push_back(e2);
				rt1075.e.push_back(e999);
				rt1075.e.push_back(e1000);
				rt1075.e.push_back(e3);
				rt1075.calc_arity(nullptr);
				sprawformtree ft1074 = std::make_shared<raw_form_tree>(elem::NONE, rt1075);
				raw_term rt1077;
				rt1077.neg = false;
				rt1077.extype = raw_term::REL;
				rt1077.e.push_back(e6);
				rt1077.e.push_back(e1);
				rt1077.e.push_back(e7);
				rt1077.e.push_back(e999);
				rt1077.e.push_back(e1003);
				rt1077.e.push_back(e243);
				rt1077.e.push_back(e3);
				rt1077.calc_arity(nullptr);
				sprawformtree ft1076 = std::make_shared<raw_form_tree>(elem::NONE, rt1077);
				sprawformtree ft1073 = std::make_shared<raw_form_tree>(elem::AND, ft1074, ft1076);
				raw_term rt1079;
				rt1079.neg = false;
				rt1079.extype = raw_term::REL;
				rt1079.e.push_back(e1011);
				rt1079.e.push_back(e1);
				rt1079.e.push_back(e1000);
				rt1079.e.push_back(e274);
				rt1079.e.push_back(e335);
				rt1079.e.push_back(e3);
				rt1079.calc_arity(nullptr);
				sprawformtree ft1078 = std::make_shared<raw_form_tree>(elem::NONE, rt1079);
				sprawformtree ft1072 = std::make_shared<raw_form_tree>(elem::AND, ft1073, ft1078);
				raw_term rt1081;
				rt1081.neg = false;
				rt1081.extype = raw_term::REL;
				rt1081.e.push_back(e930);
				rt1081.e.push_back(e1);
				rt1081.e.push_back(e243);
				rt1081.e.push_back(e1066);
				rt1081.e.push_back(e3);
				rt1081.calc_arity(nullptr);
				sprawformtree ft1080 = std::make_shared<raw_form_tree>(elem::NONE, rt1081);
				sprawformtree ft1071 = std::make_shared<raw_form_tree>(elem::AND, ft1072, ft1080);
				raw_term rt1083;
				rt1083.neg = false;
				rt1083.extype = raw_term::REL;
				rt1083.e.push_back(e600);
				rt1083.e.push_back(e1);
				rt1083.e.push_back(e274);
				rt1083.e.push_back(e335);
				rt1083.e.push_back(e243);
				rt1083.e.push_back(e1066);
				rt1083.e.push_back(e3);
				rt1083.calc_arity(nullptr);
				sprawformtree ft1082 = std::make_shared<raw_form_tree>(elem::NONE, rt1083);
				sprawformtree ft1070 = std::make_shared<raw_form_tree>(elem::AND, ft1071, ft1082);
				raw_term rt1085;
				rt1085.neg = false;
				rt1085.extype = raw_term::REL;
				rt1085.e.push_back(e800);
				rt1085.e.push_back(e1);
				rt1085.e.push_back(e274);
				rt1085.e.push_back(e335);
				rt1085.e.push_back(e3);
				rt1085.calc_arity(nullptr);
				sprawformtree ft1084 = std::make_shared<raw_form_tree>(elem::NONE, rt1085);
				sprawformtree ft1069 = std::make_shared<raw_form_tree>(elem::AND, ft1070, ft1084);
				raw_term rt1087;
				rt1087.neg = false;
				rt1087.extype = raw_term::REL;
				rt1087.e.push_back(e42);
				rt1087.e.push_back(e1);
				rt1087.e.push_back(e3);
				rt1087.calc_arity(nullptr);
				sprawformtree ft1086 = std::make_shared<raw_form_tree>(elem::NONE, rt1087);
				sprawformtree ft1068 = std::make_shared<raw_form_tree>(elem::AND, ft1069, ft1086);
				raw_rule rr1088;
				rr1088.h.push_back(rt1067);
				rr1088.set_prft(ft1068);
				raw_term rt1089;
				rt1089.neg = false;
				rt1089.extype = raw_term::REL;
				rt1089.e.push_back(e922);
				rt1089.e.push_back(e1);
				rt1089.e.push_back(e274);
				rt1089.e.push_back(e3);
				rt1089.calc_arity(nullptr);
				elem e1093;
				e1093.type = elem::VAR;
				e1093.e = d.get_lexeme("?n");
				raw_term rt1094;
				rt1094.neg = false;
				rt1094.extype = raw_term::REL;
				rt1094.e.push_back(e6);
				rt1094.e.push_back(e1);
				rt1094.e.push_back(e7);
				rt1094.e.push_back(e2);
				rt1094.e.push_back(e1093);
				rt1094.e.push_back(e274);
				rt1094.e.push_back(e3);
				rt1094.calc_arity(nullptr);
				sprawformtree ft1092 = std::make_shared<raw_form_tree>(elem::NONE, rt1094);
				raw_term rt1096;
				rt1096.neg = false;
				rt1096.extype = raw_term::REL;
				rt1096.e.push_back(e44);
				rt1096.e.push_back(e1);
				rt1096.e.push_back(e3);
				rt1096.calc_arity(nullptr);
				sprawformtree ft1095 = std::make_shared<raw_form_tree>(elem::NONE, rt1096);
				sprawformtree ft1091 = std::make_shared<raw_form_tree>(elem::AND, ft1092, ft1095);
				raw_term rt1099;
				rt1099.neg = false;
				rt1099.extype = raw_term::REL;
				rt1099.e.push_back(e52);
				rt1099.e.push_back(e1);
				rt1099.e.push_back(e3);
				rt1099.calc_arity(nullptr);
				sprawformtree ft1098 = std::make_shared<raw_form_tree>(elem::NONE, rt1099);
				sprawformtree ft1097 = std::make_shared<raw_form_tree>(elem::NOT, ft1098);
				sprawformtree ft1090 = std::make_shared<raw_form_tree>(elem::AND, ft1091, ft1097);
				raw_rule rr1100;
				rr1100.h.push_back(rt1089);
				rr1100.set_prft(ft1090);
				raw_term rt1101;
				rt1101.neg = false;
				rt1101.extype = raw_term::REL;
				rt1101.e.push_back(e67);
				rt1101.e.push_back(e1);
				rt1101.e.push_back(e2);
				rt1101.e.push_back(e274);
				rt1101.e.push_back(e3);
				rt1101.calc_arity(nullptr);
				raw_term rt1105;
				rt1105.neg = false;
				rt1105.extype = raw_term::REL;
				rt1105.e.push_back(e6);
				rt1105.e.push_back(e1);
				rt1105.e.push_back(e7);
				rt1105.e.push_back(e2);
				rt1105.e.push_back(e1093);
				rt1105.e.push_back(e274);
				rt1105.e.push_back(e3);
				rt1105.calc_arity(nullptr);
				sprawformtree ft1104 = std::make_shared<raw_form_tree>(elem::NONE, rt1105);
				raw_term rt1107;
				rt1107.neg = false;
				rt1107.extype = raw_term::REL;
				rt1107.e.push_back(e930);
				rt1107.e.push_back(e1);
				rt1107.e.push_back(e274);
				rt1107.e.push_back(e335);
				rt1107.e.push_back(e3);
				rt1107.calc_arity(nullptr);
				sprawformtree ft1106 = std::make_shared<raw_form_tree>(elem::NONE, rt1107);
				sprawformtree ft1103 = std::make_shared<raw_form_tree>(elem::AND, ft1104, ft1106);
				raw_term rt1109;
				rt1109.neg = false;
				rt1109.extype = raw_term::REL;
				rt1109.e.push_back(e44);
				rt1109.e.push_back(e1);
				rt1109.e.push_back(e3);
				rt1109.calc_arity(nullptr);
				sprawformtree ft1108 = std::make_shared<raw_form_tree>(elem::NONE, rt1109);
				sprawformtree ft1102 = std::make_shared<raw_form_tree>(elem::AND, ft1103, ft1108);
				raw_rule rr1110;
				rr1110.h.push_back(rt1101);
				rr1110.set_prft(ft1102);
				raw_term rt1111;
				rt1111.neg = false;
				rt1111.extype = raw_term::REL;
				rt1111.e.push_back(e1011);
				rt1111.e.push_back(e1);
				rt1111.e.push_back(e2);
				rt1111.e.push_back(e274);
				rt1111.e.push_back(e335);
				rt1111.e.push_back(e3);
				rt1111.calc_arity(nullptr);
				raw_term rt1116;
				rt1116.neg = false;
				rt1116.extype = raw_term::REL;
				rt1116.e.push_back(e6);
				rt1116.e.push_back(e1);
				rt1116.e.push_back(e7);
				rt1116.e.push_back(e2);
				rt1116.e.push_back(e1093);
				rt1116.e.push_back(e274);
				rt1116.e.push_back(e3);
				rt1116.calc_arity(nullptr);
				sprawformtree ft1115 = std::make_shared<raw_form_tree>(elem::NONE, rt1116);
				raw_term rt1118;
				rt1118.neg = false;
				rt1118.extype = raw_term::REL;
				rt1118.e.push_back(e1065);
				rt1118.e.push_back(e1);
				rt1118.e.push_back(e1093);
				rt1118.e.push_back(e335);
				rt1118.e.push_back(e3);
				rt1118.calc_arity(nullptr);
				sprawformtree ft1117 = std::make_shared<raw_form_tree>(elem::NONE, rt1118);
				sprawformtree ft1114 = std::make_shared<raw_form_tree>(elem::AND, ft1115, ft1117);
				raw_term rt1120;
				rt1120.neg = false;
				rt1120.extype = raw_term::REL;
				rt1120.e.push_back(e930);
				rt1120.e.push_back(e1);
				rt1120.e.push_back(e274);
				rt1120.e.push_back(e335);
				rt1120.e.push_back(e3);
				rt1120.calc_arity(nullptr);
				sprawformtree ft1119 = std::make_shared<raw_form_tree>(elem::NONE, rt1120);
				sprawformtree ft1113 = std::make_shared<raw_form_tree>(elem::AND, ft1114, ft1119);
				raw_term rt1122;
				rt1122.neg = false;
				rt1122.extype = raw_term::REL;
				rt1122.e.push_back(e44);
				rt1122.e.push_back(e1);
				rt1122.e.push_back(e3);
				rt1122.calc_arity(nullptr);
				sprawformtree ft1121 = std::make_shared<raw_form_tree>(elem::NONE, rt1122);
				sprawformtree ft1112 = std::make_shared<raw_form_tree>(elem::AND, ft1113, ft1121);
				raw_rule rr1123;
				rr1123.h.push_back(rt1111);
				rr1123.set_prft(ft1112);
				raw_term rt1124;
				rt1124.neg = false;
				rt1124.extype = raw_term::REL;
				rt1124.e.push_back(e1011);
				rt1124.e.push_back(e1);
				rt1124.e.push_back(e2);
				rt1124.e.push_back(e274);
				rt1124.e.push_back(e335);
				rt1124.e.push_back(e3);
				rt1124.calc_arity(nullptr);
				elem e1131;
				e1131.type = elem::VAR;
				e1131.e = d.get_lexeme("?a1");
				elem e1132;
				e1132.type = elem::VAR;
				e1132.e = d.get_lexeme("?a2");
				raw_term rt1133;
				rt1133.neg = false;
				rt1133.extype = raw_term::REL;
				rt1133.e.push_back(e6);
				rt1133.e.push_back(e1);
				rt1133.e.push_back(e12);
				rt1133.e.push_back(e2);
				rt1133.e.push_back(e1131);
				rt1133.e.push_back(e1132);
				rt1133.e.push_back(e3);
				rt1133.calc_arity(nullptr);
				sprawformtree ft1130 = std::make_shared<raw_form_tree>(elem::NONE, rt1133);
				raw_term rt1135;
				rt1135.neg = false;
				rt1135.extype = raw_term::EQ;
				rt1135.e.push_back(e20);
				rt1135.e.push_back(e109);
				rt1135.e.push_back(e21);
				rt1135.calc_arity(nullptr);
				sprawformtree ft1134 = std::make_shared<raw_form_tree>(elem::NONE, rt1135);
				sprawformtree ft1129 = std::make_shared<raw_form_tree>(elem::AND, ft1130, ft1134);
				raw_term rt1137;
				rt1137.neg = false;
				rt1137.extype = raw_term::REL;
				rt1137.e.push_back(e199);
				rt1137.e.push_back(e1);
				rt1137.e.push_back(e274);
				rt1137.e.push_back(e1131);
				rt1137.e.push_back(e1132);
				rt1137.e.push_back(e3);
				rt1137.calc_arity(nullptr);
				sprawformtree ft1136 = std::make_shared<raw_form_tree>(elem::NONE, rt1137);
				sprawformtree ft1128 = std::make_shared<raw_form_tree>(elem::AND, ft1129, ft1136);
				raw_term rt1139;
				rt1139.neg = false;
				rt1139.extype = raw_term::REL;
				rt1139.e.push_back(e164);
				rt1139.e.push_back(e1);
				rt1139.e.push_back(e335);
				rt1139.e.push_back(e20);
				rt1139.e.push_back(e21);
				rt1139.e.push_back(e3);
				rt1139.calc_arity(nullptr);
				sprawformtree ft1138 = std::make_shared<raw_form_tree>(elem::NONE, rt1139);
				sprawformtree ft1127 = std::make_shared<raw_form_tree>(elem::AND, ft1128, ft1138);
				raw_term rt1141;
				rt1141.neg = false;
				rt1141.extype = raw_term::REL;
				rt1141.e.push_back(e930);
				rt1141.e.push_back(e1);
				rt1141.e.push_back(e274);
				rt1141.e.push_back(e335);
				rt1141.e.push_back(e3);
				rt1141.calc_arity(nullptr);
				sprawformtree ft1140 = std::make_shared<raw_form_tree>(elem::NONE, rt1141);
				sprawformtree ft1126 = std::make_shared<raw_form_tree>(elem::AND, ft1127, ft1140);
				raw_term rt1143;
				rt1143.neg = false;
				rt1143.extype = raw_term::REL;
				rt1143.e.push_back(e44);
				rt1143.e.push_back(e1);
				rt1143.e.push_back(e3);
				rt1143.calc_arity(nullptr);
				sprawformtree ft1142 = std::make_shared<raw_form_tree>(elem::NONE, rt1143);
				sprawformtree ft1125 = std::make_shared<raw_form_tree>(elem::AND, ft1126, ft1142);
				raw_rule rr1144;
				rr1144.h.push_back(rt1124);
				rr1144.set_prft(ft1125);
				raw_term rt1145;
				rt1145.neg = false;
				rt1145.extype = raw_term::REL;
				rt1145.e.push_back(e67);
				rt1145.e.push_back(e1);
				rt1145.e.push_back(e2);
				rt1145.e.push_back(e274);
				rt1145.e.push_back(e3);
				rt1145.calc_arity(nullptr);
				raw_term rt1149;
				rt1149.neg = false;
				rt1149.extype = raw_term::REL;
				rt1149.e.push_back(e6);
				rt1149.e.push_back(e1);
				rt1149.e.push_back(e12);
				rt1149.e.push_back(e2);
				rt1149.e.push_back(e1131);
				rt1149.e.push_back(e1132);
				rt1149.e.push_back(e3);
				rt1149.calc_arity(nullptr);
				sprawformtree ft1148 = std::make_shared<raw_form_tree>(elem::NONE, rt1149);
				raw_term rt1151;
				rt1151.neg = false;
				rt1151.extype = raw_term::REL;
				rt1151.e.push_back(e199);
				rt1151.e.push_back(e1);
				rt1151.e.push_back(e274);
				rt1151.e.push_back(e1131);
				rt1151.e.push_back(e1132);
				rt1151.e.push_back(e3);
				rt1151.calc_arity(nullptr);
				sprawformtree ft1150 = std::make_shared<raw_form_tree>(elem::NONE, rt1151);
				sprawformtree ft1147 = std::make_shared<raw_form_tree>(elem::AND, ft1148, ft1150);
				raw_term rt1153;
				rt1153.neg = false;
				rt1153.extype = raw_term::REL;
				rt1153.e.push_back(e44);
				rt1153.e.push_back(e1);
				rt1153.e.push_back(e3);
				rt1153.calc_arity(nullptr);
				sprawformtree ft1152 = std::make_shared<raw_form_tree>(elem::NONE, rt1153);
				sprawformtree ft1146 = std::make_shared<raw_form_tree>(elem::AND, ft1147, ft1152);
				raw_rule rr1154;
				rr1154.h.push_back(rt1145);
				rr1154.set_prft(ft1146);
				raw_term rt1155;
				rt1155.neg = false;
				rt1155.extype = raw_term::REL;
				rt1155.e.push_back(e1011);
				rt1155.e.push_back(e1);
				rt1155.e.push_back(e2);
				rt1155.e.push_back(e274);
				rt1155.e.push_back(e335);
				rt1155.e.push_back(e3);
				rt1155.calc_arity(nullptr);
				raw_term rt1160;
				rt1160.neg = false;
				rt1160.extype = raw_term::REL;
				rt1160.e.push_back(e6);
				rt1160.e.push_back(e1);
				rt1160.e.push_back(e31);
				rt1160.e.push_back(e2);
				rt1160.e.push_back(e3);
				rt1160.calc_arity(nullptr);
				sprawformtree ft1159 = std::make_shared<raw_form_tree>(elem::NONE, rt1160);
				raw_term rt1162;
				rt1162.neg = false;
				rt1162.extype = raw_term::REL;
				rt1162.e.push_back(e155);
				rt1162.e.push_back(e1);
				rt1162.e.push_back(e274);
				rt1162.e.push_back(e3);
				rt1162.calc_arity(nullptr);
				sprawformtree ft1161 = std::make_shared<raw_form_tree>(elem::NONE, rt1162);
				sprawformtree ft1158 = std::make_shared<raw_form_tree>(elem::AND, ft1159, ft1161);
				raw_term rt1164;
				rt1164.neg = false;
				rt1164.extype = raw_term::REL;
				rt1164.e.push_back(e155);
				rt1164.e.push_back(e1);
				rt1164.e.push_back(e335);
				rt1164.e.push_back(e3);
				rt1164.calc_arity(nullptr);
				sprawformtree ft1163 = std::make_shared<raw_form_tree>(elem::NONE, rt1164);
				sprawformtree ft1157 = std::make_shared<raw_form_tree>(elem::AND, ft1158, ft1163);
				raw_term rt1166;
				rt1166.neg = false;
				rt1166.extype = raw_term::REL;
				rt1166.e.push_back(e44);
				rt1166.e.push_back(e1);
				rt1166.e.push_back(e3);
				rt1166.calc_arity(nullptr);
				sprawformtree ft1165 = std::make_shared<raw_form_tree>(elem::NONE, rt1166);
				sprawformtree ft1156 = std::make_shared<raw_form_tree>(elem::AND, ft1157, ft1165);
				raw_rule rr1167;
				rr1167.h.push_back(rt1155);
				rr1167.set_prft(ft1156);
				raw_term rt1168;
				rt1168.neg = false;
				rt1168.extype = raw_term::REL;
				rt1168.e.push_back(e67);
				rt1168.e.push_back(e1);
				rt1168.e.push_back(e2);
				rt1168.e.push_back(e274);
				rt1168.e.push_back(e3);
				rt1168.calc_arity(nullptr);
				raw_term rt1172;
				rt1172.neg = false;
				rt1172.extype = raw_term::REL;
				rt1172.e.push_back(e6);
				rt1172.e.push_back(e1);
				rt1172.e.push_back(e31);
				rt1172.e.push_back(e2);
				rt1172.e.push_back(e3);
				rt1172.calc_arity(nullptr);
				sprawformtree ft1171 = std::make_shared<raw_form_tree>(elem::NONE, rt1172);
				raw_term rt1174;
				rt1174.neg = false;
				rt1174.extype = raw_term::REL;
				rt1174.e.push_back(e155);
				rt1174.e.push_back(e1);
				rt1174.e.push_back(e274);
				rt1174.e.push_back(e3);
				rt1174.calc_arity(nullptr);
				sprawformtree ft1173 = std::make_shared<raw_form_tree>(elem::NONE, rt1174);
				sprawformtree ft1170 = std::make_shared<raw_form_tree>(elem::AND, ft1171, ft1173);
				raw_term rt1176;
				rt1176.neg = false;
				rt1176.extype = raw_term::REL;
				rt1176.e.push_back(e44);
				rt1176.e.push_back(e1);
				rt1176.e.push_back(e3);
				rt1176.calc_arity(nullptr);
				sprawformtree ft1175 = std::make_shared<raw_form_tree>(elem::NONE, rt1176);
				sprawformtree ft1169 = std::make_shared<raw_form_tree>(elem::AND, ft1170, ft1175);
				raw_rule rr1177;
				rr1177.h.push_back(rt1168);
				rr1177.set_prft(ft1169);
				elem e1178;
				e1178.type = elem::VAR;
				e1178.e = d.get_lexeme("?as1");
				elem e1179;
				e1179.type = elem::VAR;
				e1179.e = d.get_lexeme("?as2");
				raw_term rt1180;
				rt1180.neg = false;
				rt1180.extype = raw_term::REL;
				rt1180.e.push_back(e292);
				rt1180.e.push_back(e1);
				rt1180.e.push_back(e1178);
				rt1180.e.push_back(e1179);
				rt1180.e.push_back(e3);
				rt1180.calc_arity(nullptr);
				elem e1181;
				e1181.type = elem::VAR;
				e1181.e = d.get_lexeme("?bs1");
				elem e1182;
				e1182.type = elem::VAR;
				e1182.e = d.get_lexeme("?bs2");
				raw_term rt1183;
				rt1183.neg = false;
				rt1183.extype = raw_term::REL;
				rt1183.e.push_back(e238);
				rt1183.e.push_back(e1);
				rt1183.e.push_back(e1181);
				rt1183.e.push_back(e1182);
				rt1183.e.push_back(e3);
				rt1183.calc_arity(nullptr);
				elem e1187;
				e1187.type = elem::VAR;
				e1187.e = d.get_lexeme("?e2");
				raw_term rt1188;
				rt1188.neg = false;
				rt1188.extype = raw_term::REL;
				rt1188.e.push_back(e6);
				rt1188.e.push_back(e1);
				rt1188.e.push_back(e19);
				rt1188.e.push_back(e2);
				rt1188.e.push_back(e1000);
				rt1188.e.push_back(e1187);
				rt1188.e.push_back(e3);
				rt1188.calc_arity(nullptr);
				sprawformtree ft1186 = std::make_shared<raw_form_tree>(elem::NONE, rt1188);
				raw_term rt1191;
				rt1191.neg = false;
				rt1191.extype = raw_term::REL;
				rt1191.e.push_back(e1011);
				rt1191.e.push_back(e1);
				rt1191.e.push_back(e1000);
				rt1191.e.push_back(e1178);
				rt1191.e.push_back(e1181);
				rt1191.e.push_back(e3);
				rt1191.calc_arity(nullptr);
				sprawformtree ft1190 = std::make_shared<raw_form_tree>(elem::NONE, rt1191);
				raw_term rt1193;
				rt1193.neg = false;
				rt1193.extype = raw_term::REL;
				rt1193.e.push_back(e1011);
				rt1193.e.push_back(e1);
				rt1193.e.push_back(e1187);
				rt1193.e.push_back(e1179);
				rt1193.e.push_back(e1182);
				rt1193.e.push_back(e3);
				rt1193.calc_arity(nullptr);
				sprawformtree ft1192 = std::make_shared<raw_form_tree>(elem::NONE, rt1193);
				sprawformtree ft1189 = std::make_shared<raw_form_tree>(elem::AND, ft1190, ft1192);
				sprawformtree ft1185 = std::make_shared<raw_form_tree>(elem::AND, ft1186, ft1189);
				raw_term rt1195;
				rt1195.neg = false;
				rt1195.extype = raw_term::REL;
				rt1195.e.push_back(e44);
				rt1195.e.push_back(e1);
				rt1195.e.push_back(e3);
				rt1195.calc_arity(nullptr);
				sprawformtree ft1194 = std::make_shared<raw_form_tree>(elem::NONE, rt1195);
				sprawformtree ft1184 = std::make_shared<raw_form_tree>(elem::AND, ft1185, ft1194);
				raw_rule rr1196;
				rr1196.h.push_back(rt1180);
				rr1196.h.push_back(rt1183);
				rr1196.set_prft(ft1184);
				raw_term rt1197;
				rt1197.neg = false;
				rt1197.extype = raw_term::REL;
				rt1197.e.push_back(e1011);
				rt1197.e.push_back(e1);
				rt1197.e.push_back(e2);
				rt1197.e.push_back(e274);
				rt1197.e.push_back(e335);
				rt1197.e.push_back(e3);
				rt1197.calc_arity(nullptr);
				raw_term rt1203;
				rt1203.neg = false;
				rt1203.extype = raw_term::REL;
				rt1203.e.push_back(e6);
				rt1203.e.push_back(e1);
				rt1203.e.push_back(e19);
				rt1203.e.push_back(e2);
				rt1203.e.push_back(e1000);
				rt1203.e.push_back(e1187);
				rt1203.e.push_back(e3);
				rt1203.calc_arity(nullptr);
				sprawformtree ft1202 = std::make_shared<raw_form_tree>(elem::NONE, rt1203);
				raw_term rt1206;
				rt1206.neg = false;
				rt1206.extype = raw_term::REL;
				rt1206.e.push_back(e1011);
				rt1206.e.push_back(e1);
				rt1206.e.push_back(e1000);
				rt1206.e.push_back(e1178);
				rt1206.e.push_back(e1181);
				rt1206.e.push_back(e3);
				rt1206.calc_arity(nullptr);
				sprawformtree ft1205 = std::make_shared<raw_form_tree>(elem::NONE, rt1206);
				raw_term rt1208;
				rt1208.neg = false;
				rt1208.extype = raw_term::REL;
				rt1208.e.push_back(e1011);
				rt1208.e.push_back(e1);
				rt1208.e.push_back(e1187);
				rt1208.e.push_back(e1179);
				rt1208.e.push_back(e1182);
				rt1208.e.push_back(e3);
				rt1208.calc_arity(nullptr);
				sprawformtree ft1207 = std::make_shared<raw_form_tree>(elem::NONE, rt1208);
				sprawformtree ft1204 = std::make_shared<raw_form_tree>(elem::AND, ft1205, ft1207);
				sprawformtree ft1201 = std::make_shared<raw_form_tree>(elem::AND, ft1202, ft1204);
				raw_term rt1210;
				rt1210.neg = false;
				rt1210.extype = raw_term::REL;
				rt1210.e.push_back(e298);
				rt1210.e.push_back(e1);
				rt1210.e.push_back(e274);
				rt1210.e.push_back(e1178);
				rt1210.e.push_back(e1179);
				rt1210.e.push_back(e3);
				rt1210.calc_arity(nullptr);
				sprawformtree ft1209 = std::make_shared<raw_form_tree>(elem::NONE, rt1210);
				sprawformtree ft1200 = std::make_shared<raw_form_tree>(elem::AND, ft1201, ft1209);
				raw_term rt1212;
				rt1212.neg = false;
				rt1212.extype = raw_term::REL;
				rt1212.e.push_back(e245);
				rt1212.e.push_back(e1);
				rt1212.e.push_back(e335);
				rt1212.e.push_back(e1181);
				rt1212.e.push_back(e1182);
				rt1212.e.push_back(e3);
				rt1212.calc_arity(nullptr);
				sprawformtree ft1211 = std::make_shared<raw_form_tree>(elem::NONE, rt1212);
				sprawformtree ft1199 = std::make_shared<raw_form_tree>(elem::AND, ft1200, ft1211);
				raw_term rt1214;
				rt1214.neg = false;
				rt1214.extype = raw_term::REL;
				rt1214.e.push_back(e44);
				rt1214.e.push_back(e1);
				rt1214.e.push_back(e3);
				rt1214.calc_arity(nullptr);
				sprawformtree ft1213 = std::make_shared<raw_form_tree>(elem::NONE, rt1214);
				sprawformtree ft1198 = std::make_shared<raw_form_tree>(elem::AND, ft1199, ft1213);
				raw_rule rr1215;
				rr1215.h.push_back(rt1197);
				rr1215.set_prft(ft1198);
				raw_term rt1216;
				rt1216.neg = false;
				rt1216.extype = raw_term::REL;
				rt1216.e.push_back(e292);
				rt1216.e.push_back(e1);
				rt1216.e.push_back(e1178);
				rt1216.e.push_back(e1179);
				rt1216.e.push_back(e3);
				rt1216.calc_arity(nullptr);
				raw_term rt1221;
				rt1221.neg = false;
				rt1221.extype = raw_term::REL;
				rt1221.e.push_back(e6);
				rt1221.e.push_back(e1);
				rt1221.e.push_back(e19);
				rt1221.e.push_back(e2);
				rt1221.e.push_back(e1000);
				rt1221.e.push_back(e1187);
				rt1221.e.push_back(e3);
				rt1221.calc_arity(nullptr);
				sprawformtree ft1220 = std::make_shared<raw_form_tree>(elem::NONE, rt1221);
				raw_term rt1223;
				rt1223.neg = false;
				rt1223.extype = raw_term::REL;
				rt1223.e.push_back(e67);
				rt1223.e.push_back(e1);
				rt1223.e.push_back(e1000);
				rt1223.e.push_back(e1178);
				rt1223.e.push_back(e3);
				rt1223.calc_arity(nullptr);
				sprawformtree ft1222 = std::make_shared<raw_form_tree>(elem::NONE, rt1223);
				sprawformtree ft1219 = std::make_shared<raw_form_tree>(elem::AND, ft1220, ft1222);
				raw_term rt1225;
				rt1225.neg = false;
				rt1225.extype = raw_term::REL;
				rt1225.e.push_back(e67);
				rt1225.e.push_back(e1);
				rt1225.e.push_back(e1187);
				rt1225.e.push_back(e1179);
				rt1225.e.push_back(e3);
				rt1225.calc_arity(nullptr);
				sprawformtree ft1224 = std::make_shared<raw_form_tree>(elem::NONE, rt1225);
				sprawformtree ft1218 = std::make_shared<raw_form_tree>(elem::AND, ft1219, ft1224);
				raw_term rt1227;
				rt1227.neg = false;
				rt1227.extype = raw_term::REL;
				rt1227.e.push_back(e44);
				rt1227.e.push_back(e1);
				rt1227.e.push_back(e3);
				rt1227.calc_arity(nullptr);
				sprawformtree ft1226 = std::make_shared<raw_form_tree>(elem::NONE, rt1227);
				sprawformtree ft1217 = std::make_shared<raw_form_tree>(elem::AND, ft1218, ft1226);
				raw_rule rr1228;
				rr1228.h.push_back(rt1216);
				rr1228.set_prft(ft1217);
				raw_term rt1229;
				rt1229.neg = false;
				rt1229.extype = raw_term::REL;
				rt1229.e.push_back(e67);
				rt1229.e.push_back(e1);
				rt1229.e.push_back(e2);
				rt1229.e.push_back(e274);
				rt1229.e.push_back(e3);
				rt1229.calc_arity(nullptr);
				raw_term rt1235;
				rt1235.neg = false;
				rt1235.extype = raw_term::REL;
				rt1235.e.push_back(e6);
				rt1235.e.push_back(e1);
				rt1235.e.push_back(e19);
				rt1235.e.push_back(e2);
				rt1235.e.push_back(e1000);
				rt1235.e.push_back(e1187);
				rt1235.e.push_back(e3);
				rt1235.calc_arity(nullptr);
				sprawformtree ft1234 = std::make_shared<raw_form_tree>(elem::NONE, rt1235);
				raw_term rt1237;
				rt1237.neg = false;
				rt1237.extype = raw_term::REL;
				rt1237.e.push_back(e67);
				rt1237.e.push_back(e1);
				rt1237.e.push_back(e1000);
				rt1237.e.push_back(e1178);
				rt1237.e.push_back(e3);
				rt1237.calc_arity(nullptr);
				sprawformtree ft1236 = std::make_shared<raw_form_tree>(elem::NONE, rt1237);
				sprawformtree ft1233 = std::make_shared<raw_form_tree>(elem::AND, ft1234, ft1236);
				raw_term rt1239;
				rt1239.neg = false;
				rt1239.extype = raw_term::REL;
				rt1239.e.push_back(e67);
				rt1239.e.push_back(e1);
				rt1239.e.push_back(e1187);
				rt1239.e.push_back(e1179);
				rt1239.e.push_back(e3);
				rt1239.calc_arity(nullptr);
				sprawformtree ft1238 = std::make_shared<raw_form_tree>(elem::NONE, rt1239);
				sprawformtree ft1232 = std::make_shared<raw_form_tree>(elem::AND, ft1233, ft1238);
				raw_term rt1241;
				rt1241.neg = false;
				rt1241.extype = raw_term::REL;
				rt1241.e.push_back(e298);
				rt1241.e.push_back(e1);
				rt1241.e.push_back(e274);
				rt1241.e.push_back(e1178);
				rt1241.e.push_back(e1179);
				rt1241.e.push_back(e3);
				rt1241.calc_arity(nullptr);
				sprawformtree ft1240 = std::make_shared<raw_form_tree>(elem::NONE, rt1241);
				sprawformtree ft1231 = std::make_shared<raw_form_tree>(elem::AND, ft1232, ft1240);
				raw_term rt1243;
				rt1243.neg = false;
				rt1243.extype = raw_term::REL;
				rt1243.e.push_back(e44);
				rt1243.e.push_back(e1);
				rt1243.e.push_back(e3);
				rt1243.calc_arity(nullptr);
				sprawformtree ft1242 = std::make_shared<raw_form_tree>(elem::NONE, rt1243);
				sprawformtree ft1230 = std::make_shared<raw_form_tree>(elem::AND, ft1231, ft1242);
				raw_rule rr1244;
				rr1244.h.push_back(rt1229);
				rr1244.set_prft(ft1230);
				raw_term rt1245;
				rt1245.neg = false;
				rt1245.extype = raw_term::REL;
				rt1245.e.push_back(e292);
				rt1245.e.push_back(e1);
				rt1245.e.push_back(e1178);
				rt1245.e.push_back(e1179);
				rt1245.e.push_back(e3);
				rt1245.calc_arity(nullptr);
				raw_term rt1246;
				rt1246.neg = false;
				rt1246.extype = raw_term::REL;
				rt1246.e.push_back(e238);
				rt1246.e.push_back(e1);
				rt1246.e.push_back(e1181);
				rt1246.e.push_back(e1182);
				rt1246.e.push_back(e3);
				rt1246.calc_arity(nullptr);
				raw_term rt1250;
				rt1250.neg = false;
				rt1250.extype = raw_term::REL;
				rt1250.e.push_back(e6);
				rt1250.e.push_back(e1);
				rt1250.e.push_back(e26);
				rt1250.e.push_back(e2);
				rt1250.e.push_back(e1000);
				rt1250.e.push_back(e1187);
				rt1250.e.push_back(e3);
				rt1250.calc_arity(nullptr);
				sprawformtree ft1249 = std::make_shared<raw_form_tree>(elem::NONE, rt1250);
				raw_term rt1253;
				rt1253.neg = false;
				rt1253.extype = raw_term::REL;
				rt1253.e.push_back(e1011);
				rt1253.e.push_back(e1);
				rt1253.e.push_back(e1000);
				rt1253.e.push_back(e1178);
				rt1253.e.push_back(e1181);
				rt1253.e.push_back(e3);
				rt1253.calc_arity(nullptr);
				sprawformtree ft1252 = std::make_shared<raw_form_tree>(elem::NONE, rt1253);
				raw_term rt1255;
				rt1255.neg = false;
				rt1255.extype = raw_term::REL;
				rt1255.e.push_back(e1011);
				rt1255.e.push_back(e1);
				rt1255.e.push_back(e1187);
				rt1255.e.push_back(e1179);
				rt1255.e.push_back(e1182);
				rt1255.e.push_back(e3);
				rt1255.calc_arity(nullptr);
				sprawformtree ft1254 = std::make_shared<raw_form_tree>(elem::NONE, rt1255);
				sprawformtree ft1251 = std::make_shared<raw_form_tree>(elem::AND, ft1252, ft1254);
				sprawformtree ft1248 = std::make_shared<raw_form_tree>(elem::AND, ft1249, ft1251);
				raw_term rt1257;
				rt1257.neg = false;
				rt1257.extype = raw_term::REL;
				rt1257.e.push_back(e44);
				rt1257.e.push_back(e1);
				rt1257.e.push_back(e3);
				rt1257.calc_arity(nullptr);
				sprawformtree ft1256 = std::make_shared<raw_form_tree>(elem::NONE, rt1257);
				sprawformtree ft1247 = std::make_shared<raw_form_tree>(elem::AND, ft1248, ft1256);
				raw_rule rr1258;
				rr1258.h.push_back(rt1245);
				rr1258.h.push_back(rt1246);
				rr1258.set_prft(ft1247);
				raw_term rt1259;
				rt1259.neg = false;
				rt1259.extype = raw_term::REL;
				rt1259.e.push_back(e1011);
				rt1259.e.push_back(e1);
				rt1259.e.push_back(e2);
				rt1259.e.push_back(e274);
				rt1259.e.push_back(e335);
				rt1259.e.push_back(e3);
				rt1259.calc_arity(nullptr);
				raw_term rt1265;
				rt1265.neg = false;
				rt1265.extype = raw_term::REL;
				rt1265.e.push_back(e6);
				rt1265.e.push_back(e1);
				rt1265.e.push_back(e26);
				rt1265.e.push_back(e2);
				rt1265.e.push_back(e1000);
				rt1265.e.push_back(e1187);
				rt1265.e.push_back(e3);
				rt1265.calc_arity(nullptr);
				sprawformtree ft1264 = std::make_shared<raw_form_tree>(elem::NONE, rt1265);
				raw_term rt1268;
				rt1268.neg = false;
				rt1268.extype = raw_term::REL;
				rt1268.e.push_back(e1011);
				rt1268.e.push_back(e1);
				rt1268.e.push_back(e1000);
				rt1268.e.push_back(e1178);
				rt1268.e.push_back(e1181);
				rt1268.e.push_back(e3);
				rt1268.calc_arity(nullptr);
				sprawformtree ft1267 = std::make_shared<raw_form_tree>(elem::NONE, rt1268);
				raw_term rt1270;
				rt1270.neg = false;
				rt1270.extype = raw_term::REL;
				rt1270.e.push_back(e1011);
				rt1270.e.push_back(e1);
				rt1270.e.push_back(e1187);
				rt1270.e.push_back(e1179);
				rt1270.e.push_back(e1182);
				rt1270.e.push_back(e3);
				rt1270.calc_arity(nullptr);
				sprawformtree ft1269 = std::make_shared<raw_form_tree>(elem::NONE, rt1270);
				sprawformtree ft1266 = std::make_shared<raw_form_tree>(elem::ALT, ft1267, ft1269);
				sprawformtree ft1263 = std::make_shared<raw_form_tree>(elem::AND, ft1264, ft1266);
				raw_term rt1272;
				rt1272.neg = false;
				rt1272.extype = raw_term::REL;
				rt1272.e.push_back(e298);
				rt1272.e.push_back(e1);
				rt1272.e.push_back(e274);
				rt1272.e.push_back(e1178);
				rt1272.e.push_back(e1179);
				rt1272.e.push_back(e3);
				rt1272.calc_arity(nullptr);
				sprawformtree ft1271 = std::make_shared<raw_form_tree>(elem::NONE, rt1272);
				sprawformtree ft1262 = std::make_shared<raw_form_tree>(elem::AND, ft1263, ft1271);
				raw_term rt1274;
				rt1274.neg = false;
				rt1274.extype = raw_term::REL;
				rt1274.e.push_back(e245);
				rt1274.e.push_back(e1);
				rt1274.e.push_back(e335);
				rt1274.e.push_back(e1181);
				rt1274.e.push_back(e1182);
				rt1274.e.push_back(e3);
				rt1274.calc_arity(nullptr);
				sprawformtree ft1273 = std::make_shared<raw_form_tree>(elem::NONE, rt1274);
				sprawformtree ft1261 = std::make_shared<raw_form_tree>(elem::AND, ft1262, ft1273);
				raw_term rt1276;
				rt1276.neg = false;
				rt1276.extype = raw_term::REL;
				rt1276.e.push_back(e44);
				rt1276.e.push_back(e1);
				rt1276.e.push_back(e3);
				rt1276.calc_arity(nullptr);
				sprawformtree ft1275 = std::make_shared<raw_form_tree>(elem::NONE, rt1276);
				sprawformtree ft1260 = std::make_shared<raw_form_tree>(elem::AND, ft1261, ft1275);
				raw_rule rr1277;
				rr1277.h.push_back(rt1259);
				rr1277.set_prft(ft1260);
				raw_term rt1278;
				rt1278.neg = false;
				rt1278.extype = raw_term::REL;
				rt1278.e.push_back(e292);
				rt1278.e.push_back(e1);
				rt1278.e.push_back(e1178);
				rt1278.e.push_back(e1179);
				rt1278.e.push_back(e3);
				rt1278.calc_arity(nullptr);
				raw_term rt1283;
				rt1283.neg = false;
				rt1283.extype = raw_term::REL;
				rt1283.e.push_back(e6);
				rt1283.e.push_back(e1);
				rt1283.e.push_back(e26);
				rt1283.e.push_back(e2);
				rt1283.e.push_back(e1000);
				rt1283.e.push_back(e1187);
				rt1283.e.push_back(e3);
				rt1283.calc_arity(nullptr);
				sprawformtree ft1282 = std::make_shared<raw_form_tree>(elem::NONE, rt1283);
				raw_term rt1285;
				rt1285.neg = false;
				rt1285.extype = raw_term::REL;
				rt1285.e.push_back(e67);
				rt1285.e.push_back(e1);
				rt1285.e.push_back(e1000);
				rt1285.e.push_back(e1178);
				rt1285.e.push_back(e3);
				rt1285.calc_arity(nullptr);
				sprawformtree ft1284 = std::make_shared<raw_form_tree>(elem::NONE, rt1285);
				sprawformtree ft1281 = std::make_shared<raw_form_tree>(elem::AND, ft1282, ft1284);
				raw_term rt1287;
				rt1287.neg = false;
				rt1287.extype = raw_term::REL;
				rt1287.e.push_back(e67);
				rt1287.e.push_back(e1);
				rt1287.e.push_back(e1187);
				rt1287.e.push_back(e1179);
				rt1287.e.push_back(e3);
				rt1287.calc_arity(nullptr);
				sprawformtree ft1286 = std::make_shared<raw_form_tree>(elem::NONE, rt1287);
				sprawformtree ft1280 = std::make_shared<raw_form_tree>(elem::AND, ft1281, ft1286);
				raw_term rt1289;
				rt1289.neg = false;
				rt1289.extype = raw_term::REL;
				rt1289.e.push_back(e44);
				rt1289.e.push_back(e1);
				rt1289.e.push_back(e3);
				rt1289.calc_arity(nullptr);
				sprawformtree ft1288 = std::make_shared<raw_form_tree>(elem::NONE, rt1289);
				sprawformtree ft1279 = std::make_shared<raw_form_tree>(elem::AND, ft1280, ft1288);
				raw_rule rr1290;
				rr1290.h.push_back(rt1278);
				rr1290.set_prft(ft1279);
				raw_term rt1291;
				rt1291.neg = false;
				rt1291.extype = raw_term::REL;
				rt1291.e.push_back(e67);
				rt1291.e.push_back(e1);
				rt1291.e.push_back(e2);
				rt1291.e.push_back(e274);
				rt1291.e.push_back(e3);
				rt1291.calc_arity(nullptr);
				raw_term rt1297;
				rt1297.neg = false;
				rt1297.extype = raw_term::REL;
				rt1297.e.push_back(e6);
				rt1297.e.push_back(e1);
				rt1297.e.push_back(e26);
				rt1297.e.push_back(e2);
				rt1297.e.push_back(e1000);
				rt1297.e.push_back(e1187);
				rt1297.e.push_back(e3);
				rt1297.calc_arity(nullptr);
				sprawformtree ft1296 = std::make_shared<raw_form_tree>(elem::NONE, rt1297);
				raw_term rt1299;
				rt1299.neg = false;
				rt1299.extype = raw_term::REL;
				rt1299.e.push_back(e67);
				rt1299.e.push_back(e1);
				rt1299.e.push_back(e1000);
				rt1299.e.push_back(e1178);
				rt1299.e.push_back(e3);
				rt1299.calc_arity(nullptr);
				sprawformtree ft1298 = std::make_shared<raw_form_tree>(elem::NONE, rt1299);
				sprawformtree ft1295 = std::make_shared<raw_form_tree>(elem::AND, ft1296, ft1298);
				raw_term rt1301;
				rt1301.neg = false;
				rt1301.extype = raw_term::REL;
				rt1301.e.push_back(e67);
				rt1301.e.push_back(e1);
				rt1301.e.push_back(e1187);
				rt1301.e.push_back(e1179);
				rt1301.e.push_back(e3);
				rt1301.calc_arity(nullptr);
				sprawformtree ft1300 = std::make_shared<raw_form_tree>(elem::NONE, rt1301);
				sprawformtree ft1294 = std::make_shared<raw_form_tree>(elem::AND, ft1295, ft1300);
				raw_term rt1303;
				rt1303.neg = false;
				rt1303.extype = raw_term::REL;
				rt1303.e.push_back(e298);
				rt1303.e.push_back(e1);
				rt1303.e.push_back(e274);
				rt1303.e.push_back(e1178);
				rt1303.e.push_back(e1179);
				rt1303.e.push_back(e3);
				rt1303.calc_arity(nullptr);
				sprawformtree ft1302 = std::make_shared<raw_form_tree>(elem::NONE, rt1303);
				sprawformtree ft1293 = std::make_shared<raw_form_tree>(elem::AND, ft1294, ft1302);
				raw_term rt1305;
				rt1305.neg = false;
				rt1305.extype = raw_term::REL;
				rt1305.e.push_back(e44);
				rt1305.e.push_back(e1);
				rt1305.e.push_back(e3);
				rt1305.calc_arity(nullptr);
				sprawformtree ft1304 = std::make_shared<raw_form_tree>(elem::NONE, rt1305);
				sprawformtree ft1292 = std::make_shared<raw_form_tree>(elem::AND, ft1293, ft1304);
				raw_rule rr1306;
				rr1306.h.push_back(rt1291);
				rr1306.set_prft(ft1292);
				raw_prog &rp1307 = rp;
				rp1307.r.push_back(rr9);
				rp1307.r.push_back(rr16);
				rp1307.r.push_back(rr23);
				rp1307.r.push_back(rr28);
				rp1307.r.push_back(rr33);
				rp1307.r.push_back(rr41);
				rp1307.r.push_back(rr69);
				rp1307.r.push_back(rr74);
				rp1307.r.push_back(rr78);
				rp1307.r.push_back(rr96);
				rp1307.r.push_back(rr100);
				rp1307.r.push_back(rr104);
				rp1307.r.push_back(rr111);
				rp1307.r.push_back(rr116);
				rp1307.r.push_back(rr121);
				rp1307.r.push_back(rr126);
				rp1307.r.push_back(rr131);
				rp1307.r.push_back(rr136);
				rp1307.r.push_back(rr141);
				rp1307.r.push_back(rr149);
				rp1307.r.push_back(rr157);
				rp1307.r.push_back(rr163);
				rp1307.r.push_back(rr168);
				rp1307.r.push_back(rr176);
				rp1307.r.push_back(rr183);
				rp1307.r.push_back(rr190);
				rp1307.r.push_back(rr198);
				rp1307.r.push_back(rr203);
				rp1307.r.push_back(rr210);
				rp1307.r.push_back(rr217);
				rp1307.r.push_back(rr224);
				rp1307.r.push_back(rr231);
				rp1307.r.push_back(rr247);
				rp1307.r.push_back(rr268);
				rp1307.r.push_back(rr283);
				rp1307.r.push_back(rr287);
				rp1307.r.push_back(rr300);
				rp1307.r.push_back(rr316);
				rp1307.r.push_back(rr329);
				rp1307.r.push_back(rr333);
				rp1307.r.push_back(rr349);
				rp1307.r.push_back(rr369);
				rp1307.r.push_back(rr382);
				rp1307.r.push_back(rr386);
				rp1307.r.push_back(rr401);
				rp1307.r.push_back(rr417);
				rp1307.r.push_back(rr430);
				rp1307.r.push_back(rr434);
				rp1307.r.push_back(rr451);
				rp1307.r.push_back(rr472);
				rp1307.r.push_back(rr492);
				rp1307.r.push_back(rr517);
				rp1307.r.push_back(rr541);
				rp1307.r.push_back(rr561);
				rp1307.r.push_back(rr584);
				rp1307.r.push_back(rr592);
				rp1307.r.push_back(rr609);
				rp1307.r.push_back(rr627);
				rp1307.r.push_back(rr648);
				rp1307.r.push_back(rr663);
				rp1307.r.push_back(rr679);
				rp1307.r.push_back(rr685);
				rp1307.r.push_back(rr701);
				rp1307.r.push_back(rr719);
				rp1307.r.push_back(rr742);
				rp1307.r.push_back(rr765);
				rp1307.r.push_back(rr783);
				rp1307.r.push_back(rr790);
				rp1307.r.push_back(rr810);
				rp1307.r.push_back(rr834);
				rp1307.r.push_back(rr859);
				rp1307.r.push_back(rr884);
				rp1307.r.push_back(rr906);
				rp1307.r.push_back(rr916);
				rp1307.r.push_back(rr932);
				rp1307.r.push_back(rr965);
				rp1307.r.push_back(rr980);
				rp1307.r.push_back(rr987);
				rp1307.r.push_back(rr992);
				rp1307.r.push_back(rr1018);
				rp1307.r.push_back(rr1037);
				rp1307.r.push_back(rr1064);
				rp1307.r.push_back(rr1088);
				rp1307.r.push_back(rr1100);
				rp1307.r.push_back(rr1110);
				rp1307.r.push_back(rr1123);
				rp1307.r.push_back(rr1144);
				rp1307.r.push_back(rr1154);
				rp1307.r.push_back(rr1167);
				rp1307.r.push_back(rr1177);
				rp1307.r.push_back(rr1196);
				rp1307.r.push_back(rr1215);
				rp1307.r.push_back(rr1228);
				rp1307.r.push_back(rr1244);
				rp1307.r.push_back(rr1258);
				rp1307.r.push_back(rr1277);
				rp1307.r.push_back(rr1290);
				rp1307.r.push_back(rr1306);
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
