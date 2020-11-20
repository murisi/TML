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

bool driver::is_rule_conjunctive(const raw_rule &rr) {
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

bool driver::is_rule_conjunctive_with_negation(const raw_rule &rr) {
	// Ensure that there are no disjunctions
	if(rr.h.size() != 1 || rr.b.size() != 1) return false;
	// Ensure that head is positive
	if(rr.h[0].neg) return false;
	// Ensure that each body term is positive and is a relation
	for(const raw_term &rt : rr.b[0]) {
		if(rt.extype != raw_term::REL) return false;
	}
	return true;
}

/* If rr1 and rr2 are both conjunctive queries, check if there is a
 * homomorphism rr2 to rr1. By the homomorphism theorem, the existence
 * of a homomorphism implies that rr1 is contained by rr2. */

bool driver::cqc(const raw_rule &rr1, const raw_rule &rr2) {
	// Get dictionary for generating fresh symbols
	dict_t &d = tbl->get_dict();
	
	if(is_rule_conjunctive(rr1) && is_rule_conjunctive_with_negation(rr2)) {
		std::vector<raw_term> heads1 = rr1.h, bodie1 = rr1.b[0],
			heads2 = rr2.h, bodie2 = rr2.b[0];
		
		// Freeze the variables and symbols of the rule we are checking the
		// containment of
		std::map<elem, elem> freeze_map;
		raw_rule frozen_rr1 = freeze_rule(rr1, freeze_map);
		
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
	dict_t &d = tbl->get_dict();
	
	if(is_rule_conjunctive(rr1) && is_rule_conjunctive(rr2)) {
		std::vector<raw_term> heads1 = rr1.h, bodie1 = rr1.b[0],
			heads2 = rr2.h, bodie2 = rr2.b[0];
		
		// Freeze the variables and symbols of the rule we are checking the
		// containment of
		// Map from variables occuring in rr1 to frozen symbols
		std::map<elem, elem> freeze_map;
		raw_rule frozen_rr1 = freeze_rule(rr1, freeze_map);
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
		std::vector<elem> rr2_new_head = { elem::fresh_sym(d), elem_openp };
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
				raw_terms target_terms;
				// Now we want to express the homomorphism in terms of the
				// original (non-frozen) variables and terms of rr1.
				for(size_t i = 2; i < res.e.size() - 1; i++) {
					// If current variable is a body var
					if(rr2_body_vars_set.find(hd_src.e[i]) != rr2_body_vars_set.end()) {
						// Then trace the original var through the unfreeze map
						var_map[hd_src.e[i]] = unfreeze_map[res.e[i]];
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
	raw_terms aggregate(rr.h.begin(), rr.h.end());
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
		if(is_rule_conjunctive(rr2) && rr2.b[0].size() > 1) {
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
				if(is_rule_conjunctive(rr1) && cbc(rr1, rr2, homs)) {
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
			bool tmp_rel = !(exported_vars == needed_vars && count_related_rules(rr2, rp) == 1);
			
			if(tmp_rel) {
				// Variables are not exactly what is required. So make relation
				// exporting required variables and note argument order.
				target_rel = elem::fresh_sym(d);
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
	// Check that rules have correct format
	if(!(is_rule_conjunctive_with_negation(rr1) &&
		is_rule_conjunctive_with_negation(rr2))) return false;
	
	std::set<elem> vars;
	collect_positive_vars(rr1, vars);
	std::vector<std::set<elem>> partitions;
	// Do the Levy-Sagiv test
	return partition_iter(vars, partitions,
		[&](const std::vector<std::set<elem>> &partitions) -> bool {
			// Get dictionary for generating fresh symbols
			dict_t &d = tbl->get_dict();
			// Map each variable to a fresh symbol according to the partitions
			std::map<elem, elem> subs;
			for(const std::set<elem> &part : partitions) {
				elem pvar = elem::fresh_sym(d);
				for(const elem &e : part) {
					subs[e] = pvar;
				}
			}
			raw_rule subbed = freeze_rule(rr1, subs);
			std::set<elem> symbol_set;
			std::set<raw_term> canonical, canonical_negative;
			// Separate the positive and negative subgoals. Note the symbols
			// supplied to the positive subgoals.
			for(raw_term &rt : subbed.b[0]) {
				if(rt.neg) {
					rt.neg = false;
					canonical_negative.insert(rt);
					rt.neg = true;
				} else {
					canonical.insert(rt);
					for(size_t i = 2; i < rt.e.size() - 1; i++) {
						symbol_set.insert(rt.e[i]);
					}
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
	if(is_rule_conjunctive_with_negation(rr)) {
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
			if(cqc(rr, *nrr)) {
				// If the current rule is contained by a rule in reduced rules,
				// then move onto the next rule in the outer loop
				subsumed = true;
				break;
			} else if(cqc(*nrr, rr)) {
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

raw_rule driver::freeze_rule(raw_rule rr,
		std::map<elem, elem> &freeze_map) {
	for(raw_term &tm : rr.h) {
		for(elem &el : tm.e) {
			el = quote_elem(el, freeze_map);
		}
	}
	for(std::vector<raw_term> &bodie : rr.b) {
		for(raw_term &tm : bodie) {
			for(elem &el : tm.e) {
				el = quote_elem(el, freeze_map);
			}
		}
	}
	return rr;
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

/* Quote the given rule and put its quotation into the given raw_prog
 * under a relation given by rel_name. */

std::vector<elem> driver::quote_rule(const raw_rule &rr,
		const elem &rel_name, raw_prog &rp, std::map<elem, elem> &variables) {
	// Get dictionary for generating fresh symbols
	dict_t &d = tbl->get_dict();
	std::vector<elem> rule_ids;
	const elem body_id = quote_formula(rr.get_prft(), rel_name, rp, variables);
	for(int_t gidx = 0; gidx < ssize(rr.h); gidx++) {
		const elem head_id = quote_term(rr.h[gidx], rel_name, rp, variables);
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
		raw_prog &rp) {
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
					// Create the quotation relation
					quote_prog(nrp, rel_name, rp);
				}
			}
		}
	}
}

/* Essential for the handling terms/arguments in a quoted program.
 * Basically forces two interpreted terms to be equal to each other if
 * their corresponding quoted terms are equal and are both present in
 * the variable subrelation. */

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

/* Essential for the handling terms/arguments in a quoted program.
 * Basically forces an interpreted term to be equal to the corresponding
 * quoted term in the case that the quoted term does not appear in the
 * variable subrelation. */

sprawformtree driver::fix_symbols(const elem &quote_sym,
		const elem &qva, const elem &rva) {
	return std::make_shared<raw_form_tree>(elem::IMPLIES,
		std::make_shared<raw_form_tree>(elem::NOT,
			std::make_shared<raw_form_tree>(elem::NONE,
				raw_term({ quote_sym, elem_openp, elem(QVARS), qva, elem_closep }))),
		std::make_shared<raw_form_tree>(elem::NONE,
			raw_term(raw_term::EQ, {qva, elem_eq, rva})));
}

/* Interpret binary operations with varying allocations to each side.
 * Basically interprets a quoted binary relation by calling the
 * auxiliary relation to interpret each side of the quote and then
 * combining everything together using the corresponding binary logical
 * operator of the host interpreter. */
 
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

/* Enables the auxilliary interpreter relation to interpret quoted
 * quantifications. Does this by using the corresponding quantifier
 * in the host interpreter to create a variable and by handing off
 * execution of the body to the auxilliary relation. */
 
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
	raw_rule rr(head_e,
		std::make_shared<raw_form_tree>(elem::AND,
			std::make_shared<raw_form_tree>(elem::NONE, quote),
			std::make_shared<raw_form_tree>(eltype,
				std::make_shared<raw_form_tree>(elem::VAR, quantified_var),
				quant)));
	rp.r.push_back(rr);
}

/* Make interpreters that either insert terms or delete terms. Code
 * generated basically works by matching for rule quotations and using
 * the ids within it to match for the corresponding head and body
 * quotations. Next we send off the body to the auxilliary interpreter
 * relation and assign the results to a subrelation of the output
 * relation under the name given in the head. */
 
void driver::generate_rule_eval(raw_prog &rp, bool neg,
		const elem &out_rel, const elem &quote_sym, const elem &aux_rel,
		const std::vector<elem> &iparams, const std::vector<elem> &qparams,
		const std::vector<elem> &iargs, const std::vector<elem> &qargs) {
	// Get dictionary for generating fresh variables
	dict_t &d = tbl->get_dict();
	
	int_t arity_num = qparams.size();
	const elem rule_name = elem::fresh_var(d), elt_id = elem::fresh_var(d),
		head_id = elem::fresh_var(d), head2_id = elem::fresh_var(d),
		body_id = elem::fresh_var(d);
	
	for(int_t a = 0; a < arity_num+1; a++) {
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
		sprawformtree head =
			std::make_shared<raw_form_tree>(elem::NONE, raw_term(qhead_e));
		// If neg flag is set, then the head of the rule is actually a
		// negation pointing to the positive part of the head
		if(neg) {
			// Modify positive head to not directly use id in rule quote
			head->rt->e[3] = head2_id;
			// Instead make an intermediate term to extract positive head part
			// from negation
			head = std::make_shared<raw_form_tree>(elem::AND, head,
				std::make_shared<raw_form_tree>(elem::NONE,
					raw_term({ quote_sym, elem_openp, elem(QNOT), head_id,
						head2_id, elem_closep })));
		}
		// Make the body interpretation
		std::vector<elem> body_e = { aux_rel, elem_openp, body_id };
		for(int_t i = 0; i < arity_num; i++) {
			body_e.push_back(qargs[i]);
			body_e.push_back(iargs[i]);
		}
		body_e.push_back(elem_closep);
		sprawformtree bodie =
			std::make_shared<raw_form_tree>(elem::AND,
				std::make_shared<raw_form_tree>(elem::AND,
					std::make_shared<raw_form_tree>(elem::NONE, qrule), head),
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
		if(neg) rt.neg = true;
		raw_rule rr(rt, bodie);
		rp.r.push_back(rr);
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
			
			// Allocate rule name, rule id, head id, body id
			elem rule_name = elem::fresh_var(d), elt_id = elem::fresh_var(d),
				forma_id = elem::fresh_var(d);
			// Allocate interpreted and quoted arguments
			std::vector<elem> iparams, qparams, iargs, qargs;
			for(int_t a = 0; a < arity_num.num; a++) {
				iargs.push_back(elem::fresh_var(d));
				qargs.push_back(elem::fresh_var(d));
				iparams.push_back(elem::fresh_var(d));
				qparams.push_back(elem::fresh_var(d));
			}
			// Separate the internal rules used to execute parts of a quoted
			// rule from the external rules put in the out relation. This way
			// the construction of the next stage does not interfere with
			// the execution of the current stage.
			raw_prog ext_prog, int_prog;
			
			// Make the interpreters that insert terms
			generate_rule_eval(ext_prog, false, out_rel, quote_sym, aux_rel,
				iparams, qparams, iargs, qargs);
			// Make the interpreters that delete terms
			generate_rule_eval(ext_prog, true, out_rel, quote_sym, aux_rel,
				iparams, qparams, iargs, qargs);
			
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
				raw_rule rr(head, bodie);
				int_prog.r.push_back(rr);
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
				raw_rule rr(head_e,
					std::make_shared<raw_form_tree>(elem::AND,
						std::make_shared<raw_form_tree>(elem::AND,
							std::make_shared<raw_form_tree>(elem::NONE, quote),
							std::make_shared<raw_form_tree>(elem::NONE, equals)),
						std::make_shared<raw_form_tree>(elem::AND,
							fix_symbols(quote_sym, qparams[0], iparams[0]),
							fix_symbols(quote_sym, qparams[1], iparams[1]))));
				int_prog.r.push_back(rr);
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
				raw_rule rr(head_e,
					std::make_shared<raw_form_tree>(elem::AND,
						std::make_shared<raw_form_tree>(elem::NONE, quote),
						std::make_shared<raw_form_tree>(elem::NOT,
							std::make_shared<raw_form_tree>(elem::NONE, neg_e))));
				int_prog.r.push_back(rr);
			}
			
			// Interpret conjunctions
			generate_binary_eval(int_prog, QAND, elem::AND, quote_sym, und_sym,
				aux_rel, iparams, qparams);
			// Interpret disjunctions
			generate_binary_eval(int_prog, QALT, elem::ALT, quote_sym, und_sym,
				aux_rel, iparams, qparams);
			// Interpret implies
			generate_binary_eval(int_prog, QIMPLIES, elem::IMPLIES, quote_sym, und_sym,
				aux_rel, iparams, qparams);
			// Interpret coimplies
			generate_binary_eval(int_prog, QCOIMPLIES, elem::COIMPLIES, quote_sym, und_sym,
				aux_rel, iparams, qparams);
			
			// Interpret forall
			generate_quantified_eval(int_prog, QFORALL, elem::FORALL, quote_sym,
				aux_rel, iparams, qparams);
			// Interpret exists
			generate_quantified_eval(int_prog, QEXISTS, elem::EXISTS, quote_sym,
				aux_rel, iparams, qparams);
			// Interpret unique
			generate_quantified_eval(int_prog, QUNIQUE, elem::UNIQUE, quote_sym,
				aux_rel, iparams, qparams);
			
			// Now add the internal and external programs to the output
			// program.
			rp.nps.push_back(int_prog);
			rp.nps.push_back(ext_prog);
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

/* Convenience function for getting relation name and arity from
 * term. */

std::tuple<elem, int_t> get_relation_info(const raw_term &rt) {
	return std::make_tuple(rt.e[0], rt.e.size() - 3);
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
	
	std::map<elem, elem> freeze_map, unfreeze_map;
	// Separate the internal rules used to execute the parts of the
	// transformation from the external rules used to expose the results
	// of computation.
	raw_prog ext_prog;
	// Create a duplicate of each rule in the given program under a
	// generated alias.
	for(raw_rule &rr : rp.r) {
		for(raw_term &rt : rr.h) {
			raw_term rt2 = rt;
			auto it = freeze_map.find(rt.e[0]);
			if(it != freeze_map.end()) {
				rt.e[0] = it->second;
			} else {
				elem frozen_elem = elem::fresh_sym(d);
				// Store the mapping so that the derived portion of each
				// relation is stored in exactly one place
				unfreeze_map[frozen_elem] = rt.e[0];
				rt.e[0] = freeze_map[rt.e[0]] = frozen_elem;
			}
			// Update the external interface
			ext_prog.r.push_back(raw_rule(rt2, rt));
		}
	}
	// Execute the transformation on the renamed rules.
	f(rp);
	
	// Partition the rules by relations
	typedef std::set<raw_rule> relation;
	std::map<std::tuple<elem, int_t>, relation> rels;
	for(const raw_rule &rr : rp.r) {
		rels[get_relation_info(rr.h[0])].insert(rr);
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
					std::tuple<elem, int_t> target = get_relation_info(rt);
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
		// Push nested programs containing the internal rules onto the
		// program in execution order
		for(const std::set<const relation *> v : sorted) {
			raw_prog np;
			for(const relation *w : v) {
				for(const raw_rule &rr : *w) {
					np.r.push_back(rr);
				}
			}
			rp.nps.push_back(np);
		}
		// Add the external program which serves to writeback the outputs of
		// the internal rules.
		rp.nps.push_back(ext_prog);
		rp.r.clear();
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

/* Make a term with behavior equivalent to the supplied first order
 * logic formula with the given bound variables. This might involve
 * adding temporary relations to the given program. */

raw_term driver::to_pure_tml(const sprawformtree &t,
		std::vector<raw_rule> &rp) {
	// Get dictionary for generating fresh symbols
	dict_t &d = tbl->get_dict();
	const elem part_id = elem::fresh_sym(d);
	// Determine the variables that our subformula is parameterized by,
	// our new rule would need to receive this.
	std::set<elem> fv;
	std::vector<elem> bound_vars = {};
	populate_free_variables(*t, bound_vars, fv);
	
	switch(t->type) {
		case elem::IMPLIES:
			// Implication is logically equivalent to the following
			return to_pure_tml(std::make_shared<raw_form_tree>(elem::ALT,
				std::make_shared<raw_form_tree>(elem::NOT, t->l), t->r), rp);
		case elem::COIMPLIES:
			// Co-implication is logically equivalent to the following
			return to_pure_tml(std::make_shared<raw_form_tree>(elem::AND,
				std::make_shared<raw_form_tree>(elem::IMPLIES, t->l, t->r),
				std::make_shared<raw_form_tree>(elem::IMPLIES, t->r, t->l)), rp);
		case elem::AND: {
			// Collect all the conjuncts within the tree top
			std::vector<sprawformtree> ands;
			flatten_associative(elem::AND, t, ands);
			std::vector<raw_term> terms;
			// And make a pure TML formula listing them
			for(const sprawformtree &tree : ands) {
				terms.push_back(to_pure_tml(tree, rp));
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
				raw_rule nr(raw_term(part_id, fv), to_pure_tml(tree, rp));
				rp.push_back(nr);
			}
			break;
		} case elem::NOT: {
			raw_term nt = to_pure_tml(t->l, rp);
			nt.neg = true;
			return nt;
		} case elem::EXISTS: {
			// Make the proposition that is being quantified
			raw_term nrt = to_pure_tml(t->r, rp);
			// Replace occurences of the quantified variable in the arguments
			// with a fresh variable to avoid unnecessary constraints.
			const elem qvar = *(t->l->el);
			const elem ne = elem::fresh_var(d);
			for(elem &e : nrt.e) {
				if(e == qvar) {
					e = ne;
				}
			}
			// Make the rule corresponding to this existential formula
			raw_rule nr(raw_term(part_id, fv), nrt);
			rp.push_back(nr);
			break;
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
							raw_term(raw_term::EQ, { evar, elem_eq, qvar }))))), rp);
		} case elem::NONE: {
			return *t->rt;
		} case elem::FORALL: {
			// The universal quantifier is logically equivalent to the
			// following
			elem qvar = *(t->l->el);
			return to_pure_tml(std::make_shared<raw_form_tree>(elem::NOT,
				std::make_shared<raw_form_tree>(elem::EXISTS,
					std::make_shared<raw_form_tree>(elem::VAR, qvar),
					std::make_shared<raw_form_tree>(elem::NOT, t->r))), rp);
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
			rr.set_b({{to_pure_tml(rr.prft, rp.r)}});
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

void driver::populate_free_variables(const raw_term &t,
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

void driver::populate_free_variables(const raw_form_tree &t,
		std::vector<elem> &bound_vars, std::set<elem> &free_vars) {
	switch(t.type) {
		case elem::IMPLIES: case elem::COIMPLIES: case elem::AND:
		case elem::ALT:
			populate_free_variables(*t.l, bound_vars, free_vars);
			populate_free_variables(*t.r, bound_vars, free_vars);
			break;
		case elem::NOT:
			populate_free_variables(*t.l, bound_vars, free_vars);
			break;
		case elem::EXISTS: case elem::UNIQUE: case elem::FORALL: {
			elem elt = *(t.l->el);
			bound_vars.push_back(elt);
			populate_free_variables(*t.r, bound_vars, free_vars);
			bound_vars.pop_back();
			break;
		} case elem::NONE: {
			populate_free_variables(*t.rt, bound_vars, free_vars);
			break;
		} default:
			assert(false); //should never reach here
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
	reduce_universe(var, *rul.get_prft(), universe, database);
}

/* Based on the current state of the database, use static analysis of
 * the logical formulas to remove from the universe of each quantification,
 * elements that could never satisfy their inner formula. */

void driver::populate_universes(const raw_form_tree &t,
		std::set<elem> &universe,
		std::map<const elem*, std::set<elem>> &universes,
		std::set<raw_term> &database) {
	switch(t.type) {
		case elem::IMPLIES: case elem::COIMPLIES: case elem::AND:
		case elem::ALT:
			populate_universes(*t.l, universe, universes, database);
			populate_universes(*t.r, universe, universes, database);
			break;
		case elem::NOT:
			populate_universes(*t.l, universe, universes, database);
			break;
		case elem::EXISTS: case elem::UNIQUE: case elem::FORALL: {
			populate_universes(*t.r, universe, universes, database);
			std::set<elem> universe2 = universe;
			const elem &elt = *(t.l->el);
			reduce_universe(elt, *t.r, universe2, database);
			universes[&elt] = universe2;
			break;
		} case elem::NONE:
			break;
		default:
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
	populate_universes(*rul.get_prft(), universe, universes, database);
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
		if(evaluate_form_tree(*rul.get_prft(), universes, bindings, database)) {
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
		case elem::IMPLIES: case elem::COIMPLIES: case elem::AND:
		case elem::ALT:
			populate_universe(t->l, universe);
			populate_universe(t->r, universe);
			break;
		case elem::NOT:
			populate_universe(t->l, universe);
			break;
		case elem::EXISTS: case elem::UNIQUE: case elem::FORALL: {
			populate_universe(t->r, universe);
			break;
		} case elem::NONE:
			populate_universe(*t->rt, universe);
			break;
		default:
			assert(false); //should never reach here
	}
}

void driver::populate_universe(const raw_prog &rp,
		std::set<elem> &universe) {
	for(const raw_rule &rr : rp.r) {
		for(const raw_term &rt : rr.h) {
			populate_universe(rt, universe);
		}
		populate_universe(rr.get_prft(), universe);
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
	
	for (auto& np : rp.nps) if (!transform(np, pd.strs)) return false;
	
	recursive_transform(rp, [&](raw_prog &rp) {
		simplify_formulas(rp);
		std::cout << "Simplified Program:" << std::endl << std::endl << rp << std::endl;
		transform_quotes(rp);
		std::cout << "Quoted Program:" << std::endl << std::endl << rp << std::endl;
		transform_evals(rp);
		std::cout << "Evaled Program:" << std::endl << std::endl << rp << std::endl;
		//quote_prog(rp, elem(elem::SYM, get_lexeme("this")), rp);
		//std::cout << "TML Program With this:" << std::endl << std::endl << rp << std::endl;
		step_transform(rp, [&](raw_prog &rp) {
			to_pure_tml(rp);
			std::cout << "Pure TML Program:" << std::endl << std::endl << rp << std::endl;
			subsume_queries(rp);
			std::cout << "Minimized Program:" << std::endl << std::endl << rp << std::endl;
			factor_rules(rp);
			std::cout << "Factorized Program:" << std::endl << std::endl << rp << std::endl;
		});
	});
	/*std::set<elem> universe;
	std::set<raw_term> database;
	naive_pfp(p, universe, database);
	std::cout << "Fixed Point:" << std::endl << std::endl;
	for(const raw_term &entry : database) {
		std::cout << entry << "." << std::endl;
	}*/
	std::cout << std::endl << std::endl;
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
