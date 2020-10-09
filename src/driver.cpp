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
	throw 0; // unreachable
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

/* Holds the ever-growing program text. This object cannot be isolated to the
 * code where command line arguments are parsed, because the "eval" relation
 * constantly creates more program text that needs to be parsed and kept alive
 * till the program's termination.
 */

inputs tmpii;

/* Takes a raw term and its position in the program to be quoted and returns
 * its quotation within a relation of the given name. The locations of variable
 * elements within the raw term are added to the variables vector. */

raw_term driver::quote_term(const raw_term &head, const elem &rel_name, int rule_idx, int disjunct_idx, int goal_idx, std::vector<std::tuple<int, int, int, int>> &variables) {
	// We'll need the dict when we're creating terms with parentheses
	dict_t &dict = tbl->get_dict();
	// The elements of the term that we're building up
	std::vector<elem> quoted_term_e;
	// Add metadata to quoted term: term signature, rule #, disjunct #, goal #, relation sym
	quoted_term_e.insert(quoted_term_e.end(),
		{rel_name, elem(elem::OPENP, dict.op), elem(0), elem(rule_idx), elem(disjunct_idx), elem(goal_idx), head.e[0] });
	for(std::vector<elem>::size_type param_idx = 2; param_idx < head.e.size() - 1; param_idx ++) {
		if(head.e[param_idx].type == elem::VAR) {
			// Convert the variable to a symbol and add it to quouted term
			elem var_sym_elem(elem::SYM, head.e[param_idx].e);
			quoted_term_e.push_back(var_sym_elem);
			// Log the fact that a variable occurs at this location
			variables.emplace_back(rule_idx, disjunct_idx, goal_idx, param_idx-2);
		} else {
			quoted_term_e.push_back(head.e[param_idx]);
		}
	}
	// Terminate term elements and make raw_term object
	quoted_term_e.push_back(elem(elem::CLOSEP, dict.cl));
	raw_term quoted_term;
	quoted_term.e = quoted_term_e;
	// We can call calc_arity with nullptr because no validation error will
	// occur because we've already done validation here.
	quoted_term.calc_arity(nullptr);
	return quoted_term;
}

/* Read a vector of elements up until an unmatched closing parenthesis and
 * parse what was read into a raw_prog. */

raw_prog driver::read_prog(std::vector<elem>::const_iterator iter, std::vector<elem>::const_iterator end, const raw_prog &rp, std::vector<elem>::const_iterator &prog_end) {
	stringstream quote_tmp;
	// Number of nested parentheses we're in.
	int nest_level = 1;
	// Capture the rule argument to quote by adding all lexemes until
	// closing parenthesis of rule to a string.
	for(; iter != end && nest_level; iter ++) {
		if(iter->type == elem::OPENP) nest_level++;
		else if(iter->type == elem::CLOSEP) nest_level--;
		// Make sure this lexeme is not the closing parenthesis that wraps
		// the entire rule.
		if(nest_level) {
			// Lexer does not allow the turnstile operator ":-" and comma
			// operator "," inside rules, so we'll look for the lexemes "ts"
			// and "cm" for now.
			string_t elem_str = lexeme2str(iter->e);
			if(iter->type == elem::SYM && to_string_t("ts") == elem_str) {
				quote_tmp << ":- ";
			} else if(iter->type == elem::SYM && to_string_t("cm") == elem_str) {
				quote_tmp << ", ";
			} else if(iter->type == elem::SYM && to_string_t("dt") == elem_str) {
				quote_tmp << ". ";
			} else {
				quote_tmp << *iter << " ";
			}
		}
	}
	// If we have not managed to reach the parenthesis that encloses the entire
	// rule being supplied to quote, then the supplied vector could not have
	// been a representation of a rule.
	if(nest_level) {
		exit(1);
	} else {
		input *prog_in = tmpii.add_string(quote_tmp.str());
		prog_in->prog_lex();
		raw_prog nrp;
		nrp.builtins = rp.builtins;
		// Try to parse the string that we have been building using elems.
		nrp.parse(prog_in);
		prog_end = iter - 1;
		return nrp;
	}
}

/* Loop through the rules of the given program checking if they use a function
 * called "quote" in their bodies. Quote's first argument is the relation into
 * which it should put the quotation it creates, and it's second argument is the
 * rule to quote. Say that the output relation name is s, quote will populate it
 * according to the following schema:
 * For each context, each N-ary term is stored as:
 * s(0 <rule #> <disjunct #> <goal #> <relname> <input0> <input1> ... <inputN>)
 * The locations of the variables in the above schema are stored as:
 * s(1 <rule #> <disjunct #> <goal #> <input #>) */

void driver::transform_quotes(raw_prog &rp) {
	// We'll need the dict when we're creating terms with parentheses
	dict_t &dict = tbl->get_dict();
	for(raw_rule &outer_rule : rp.r) {
		// Iterate through the bodies of the current rule looking for uses of the
		// "quote" relation.
		for(std::vector<raw_term> &bodie : outer_rule.b) {
			for(raw_term &rhs_term : bodie) {
				// Search for uses of quote within a relation.
				for(std::vector<elem>::size_type offset = 2; offset < rhs_term.e.size(); offset ++) {
					if(rhs_term.e[offset].type == elem::SYM && to_string_t("quote") == lexeme2str(rhs_term.e[offset].e)) {
						// The parenthesis marks the beginning of quote's arguments.
						if(rhs_term.e.size() > offset + 1 && rhs_term.e[offset + 1].type == elem::OPENP) {
							std::vector<elem>::const_iterator prog_end;
							raw_prog nrp = read_prog(rhs_term.e.begin() + offset + 3, rhs_term.e.end(), rp, prog_end);
							// The relation under which the quotation we build will be stored.
							elem rel_name = rhs_term.e[offset + 2];
							// Replace the whole quotation with the relation it will create.
							rhs_term.e.erase(rhs_term.e.begin() + offset, prog_end + 1);
							rhs_term.e.insert(rhs_term.e.begin() + offset, rel_name);
							rhs_term.calc_arity(nullptr);
							// Maintain a list of locations where variables occur:
							// (rule #, disjunction #, goal #, elem #)
							std::vector<std::tuple<int, int, int, int>> variables;
							// Maintain the current rule index of rules being quoted
							int rule_idx = 0;
							for(const raw_rule &rr : nrp.r) {
								// We are going to make a separate quoted rule with identical body
								// for each head of the supplied rule.
								for(const raw_term &head : rr.h) {
									rp.r.push_back(raw_rule(quote_term(head, rel_name, rule_idx, 0, 0, variables)));
									// Maintain the current disjunction index of the bodies being quoted
									int disjunct_idx = 1;
									for(const std::vector<raw_term> &bodie : rr.b) {
										// Maintain the current goal index of the disjunction being quoted
										int goal_idx = 0;
										for(const raw_term &goal : bodie) {
											rp.r.push_back(raw_rule(quote_term(goal, rel_name, rule_idx, disjunct_idx, goal_idx, variables)));
											goal_idx ++;
										}
										disjunct_idx ++;
									}
									rule_idx ++;
								}
							}
							
							// Now create sub-relation to store the location of variables in the quoted relation
							for(auto const& [rule_idx, disjunct_idx, goal_idx, arg_idx] : variables) {
								std::vector<elem> var_e =
									{ rel_name, elem(elem::OPENP, dict.op), elem(1), elem(rule_idx), elem(disjunct_idx), elem(goal_idx), elem(arg_idx), elem(elem::CLOSEP, dict.cl) };
								raw_term var_t;
								var_t.e = var_e;
								var_t.calc_arity(nullptr);
								rp.r.push_back(raw_rule(var_t));
							}
						}
					}
				}
			}
		}
	}
}

/* Loop through the rules of the given program checking if they use a relation
 * called "eval" in their bodies. If eval is used, take its single argument,
 * the name of a relation containing a representation of a TML program, and
 * append to the current program the program represented by the relation.
 * See driver::transform_quotes for the schema of the relation. */

void driver::transform_evals(raw_prog &rp) {
	// We'll need the dict when we're creating terms with parentheses
	dict_t &dict = tbl->get_dict();
	for(raw_rule &outer_rule : rp.r) {
		// Iterate through the bodies of the current rule looking for uses of the
		// "eval" relation.
		for(std::vector<raw_term> &bodie : outer_rule.b) {
			for(raw_term &rhs_term : bodie) {
				if(rhs_term.e[0].type == elem::SYM && to_string_t("eval") == lexeme2str(rhs_term.e[0].e)) {
					// The first parenthesis marks the beginning of eval's arguments, the
					// second marks the beginning of the rule being supplied to eval.
					if(rhs_term.e.size() == 4 && rhs_term.e[1].type == elem::OPENP && rhs_term.e[3].type == elem::CLOSEP) {
						// The relation containing the quotation is in between the parentheses
						elem quote_rel = rhs_term.e[2];
						// Ultimately we want to recreate raw_rules from the unordered facts in the
						// given relation. So let's first look for the entries of the given relation
						// and store them in an ordered map. Also store the variable locations.
						std::map<std::tuple<int, int, int>, raw_term> quote_map;
						std::vector<std::tuple<int, int, int, int>> var_locs;
						for(raw_rule &rr : rp.r) {
							if(lexeme2str(rr.h[0].e[0].e) == lexeme2str(quote_rel.e)) {
								if(rr.h[0].e[2].num == 0) {
									quote_map[std::make_tuple(rr.h[0].e[3].num, rr.h[0].e[4].num, rr.h[0].e[5].num)] = rr.h[0];
								} else if(rr.h[0].e[2].num == 1) {
									var_locs.push_back(std::make_tuple(rr.h[0].e[3].num, rr.h[0].e[4].num, rr.h[0].e[5].num, rr.h[0].e[6].num));
								}
							}
						}
						std::tuple<int, int, int> prev_pos { -1, 0, 0 };
						std::vector<raw_rule> reconstr_rules;
						// Reconstruct the quoted rules. Since the body of this loop is doing the
						// reconstructions in-order, it is important that the terms are iterated in
						// lexicographic order.
						for(auto const& [pos, rt] : quote_map) {
							// Each fact in the quote map corresponds to a term. Reconstruct this term.
							raw_term reconstr_term;
							reconstr_term.e.push_back(rt.e[6]);
							reconstr_term.e.push_back(elem(elem::OPENP, dict.op));
							reconstr_term.e.insert(reconstr_term.e.end(), rt.e.begin() + 7, rt.e.end() - 1);
							reconstr_term.e.push_back(elem(elem::CLOSEP, dict.cl));
							reconstr_term.calc_arity(nullptr);
							// Now figure out which rule and where in the rule to put this term.
							if(get<0>(pos) != get<0>(prev_pos)) {
								// Case where we have encountered new rule in map
								raw_rule rr;
								rr.h.push_back(reconstr_term);
								reconstr_rules.push_back(rr);
							} else if(get<1>(pos) != get<1>(prev_pos)) {
								// Case where we have encountered new disjunct in map
								std::vector<raw_term> disjunct;
								disjunct.push_back(reconstr_term);
								reconstr_rules.back().b.push_back(disjunct);
							} else if(get<2>(pos) != get<2>(prev_pos)) {
								// Case where we have encountered new goal in map
								// If the body is empty, we must still be constructing the head terms
								if(reconstr_rules.back().b.empty()) {
									reconstr_rules.back().h.push_back(reconstr_term);
								} else {
									reconstr_rules.back().b.back().push_back(reconstr_term);
								}
							}
							prev_pos = pos;
						}
						// During quotation, variables in the program being quoted were turned to
						// symbols. So now let's use the variable markers to turn the symbols back
						// to variables.
						for(auto const& [rule_idx, disjunct_idx, goal_idx, elem_idx] : var_locs) {
							// The zeroth disjunct index is special as it refers to the rule head
							if(disjunct_idx == 0) {
								reconstr_rules[rule_idx].h[goal_idx].e[elem_idx + 2].type = elem::VAR;
							} else {
								reconstr_rules[rule_idx].b[disjunct_idx - 1][goal_idx].e[elem_idx + 2].type = elem::VAR;
							}
						}
						// Now add the reconstructed rules to the program.
						for(const raw_rule &rr : reconstr_rules) {
							rp.r.push_back(rr);
						}
					}
				}
			}
		}
	}
}

void driver::transform(raw_progs& rp, size_t n, const strs_t& /*strtrees*/) {
	if (!rp.p.size()) return;
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
		if (pd.strs.size() > 1) er(err_one_input);
//		else transform_grammar(rp.p[n], pd.strs.begin()->first,
//			pd.strs.begin()->second.size());
//	}
//	if (opts.enabled("sdt"))
//		for (raw_prog& p : rp.p)
//			p = transform_sdt(move(p));
	for (raw_prog& p : rp.p) {
		transform_quotes(p);
		transform_evals(p);
	}
#ifdef TRANSFORM_BIN_DRIVER
	if (opts.enabled("bin"))
		for (raw_prog& p : rp.p)
			transform_bin(p);
#endif
//	if (trel[0]) transform_proofs(rp.p[n], trel);
	//o::out()<<rp.p[n]<<endl;
//	if (pd.bwd) rp.p.push_back(transform_bwd(rp.p[n]));
}

void driver::output_pl(const raw_prog& p) const {
	if (opts.enabled("xsb"))     print_xsb(o::to("xsb"), p);
	if (opts.enabled("swipl"))   print_swipl(o::to("swipl"),   p);
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
	o::ms() << "# elapsed: ";
	measure_time_end();
	pd.elapsed_steps = nsteps() - step;
	//if (pd.elapsed_steps > 0 && steps && pd.elapsed_steps > steps) throw 0;
//	for (auto x : prog->strtrees_out)
//		strtrees.emplace(x.first, get_trees(prog->pd.strtrees[x.first],
//					x.second, prog->rng.bits));
	return fp;
}

void driver::add(input* in) {
	rp.parse(in, tbl->get_dict(), in->newseq);
	if (!in->newseq) transform(rp, pd.n, pd.strs);
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
	//if (opts.enabled("t")) o::to("transformed")
	//	<< "# Transformed program " << pd.n + 1 << ":" << endl
	//	<< '{' << endl << p << '}' << endl;
}

void driver::restart() {
	pd.n = 0;
	pd.start_step = nsteps();
	running = true;
}

bool driver::run(size_t steps, size_t break_on_step, bool break_on_fp) {
	try {
		if (!rp.p.size()) return true;
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
	} catch (unsat_exception& e) {
		o::out() << e.what() << endl;
		result = false;
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
	if (ii->size()) throw_runtime_error( // TODO
		"Loading into a running program is not yet supported.");
	load_archives.emplace_back(archive::type::DRIVER, filename, 0, false);
	load_archives.back() >> *this;
}

void driver::save(std::string filename) {
	archive ar(archive::type::DRIVER, filename, archive::size(*this),
		true);
	ar << *this;
}

void driver::read_inputs() {
	//COUT << "read_inputs() current_input: " << current_input << " next_input: " << (current_input ? current_input->next() : 0) << endl;
	while (current_input && current_input->next()) {
		current_input = current_input->next();
		add(current_input);
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
		if (current_input) add(current_input);
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
