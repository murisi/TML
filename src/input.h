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
#ifndef __INPUT_H__
#define __INPUT_H__

#include <vector>
#include <set>
#include <array>
#include <cstring>
#include <iostream>
#include <memory>
#include <sys/stat.h>

#include "defs.h"
#include "dict.h"
#include "memory_map.h"

class archive;
#define lexeme2str(l) string_t((l)[0], (l)[1]-(l)[0])

typedef std::pair<int_t, bool> guard;

/**
 * input class contains input data. input can be one of three types: STDIN,
 * FILE or STRING. STDIN works as a STRING which is read from the standard input
 * FILE uses system's memory mapping to access file data.
 * STDIN and STRING inputs from command line options and repl queries are
 * allocated and are freed when input is deconstructed.
 * STRING inputs loaded from archives are pointed to file's mmap. 
 */
struct input {
	friend class archive;
	enum type { STDIN, FILE, STRING } type_; // input type
	bool newseq = false; // input is understood as a new prog sequence
	size_t offset = 0;   // offset of this input from the beginning
	size_t pos = 0;      // position of the currently parsed lexeme
	lexemes l = {};      // lexemes scanned from the input data
	bool error = false;  // parse error in the input's data
	/**
	 * STDIN input constructor
	 * @param ns - if true this input would be added as a new sequence ({})
	 */
	input(bool ns = false) : type_(STDIN), newseq(ns), beg_(0), data_(0),
		size_(load_stdin()) {
		//COUT << "created stdin input *: " << beg_ << std::endl;
	}
	/**
	 * STRING input constructor - without allocation (input from a mmap)
	 * @param s - pointer to a utf8 encoded input data
	 * @param sz - size of the input data
	 * @param ns - set ns true for making the input a new prog sequence
	 */
	input(void* s, size_t sz, bool ns = false) : type_(STRING), newseq(ns),
		beg_((ccs) s), data_(beg_), size_(sz), allocated_(false) {
		//COUT << "created pointer input: " << beg_ << std::endl;
	}
	/**
	 * STRING input constructor - with allocation
	 * @param s - pointer to a utf8 encoded input data
	 * @param ns - set ns true for making the input a new prog sequence
	 */
	input(ccs s, bool ns = false) : type_(STRING), newseq(ns),
		beg_(strdup(s)),data_(beg_),size_(strlen(beg_)),allocated_(true)
	{	//COUT << "created string input *: " << s << std::endl;
	}
	/**
	 * FILE input constructor
	 * @param f - file name
	 * @param ns - set ns true for making the input a new prog sequence
	 */
	input(std::string f, bool ns = false); // FILE
	/**
	 * destructor frees allocated data if any
	 */
	~input();
	/**
	 * lex scans a lexeme in a data pointer s and iterates it
	 * @param s - pointer to the input data
	 * @return scanned lexeme
	 */
	lexeme lex(pccs s);
	/**
	 * scans input's data for lexemes
	 * @return scanned lexemes
	 */
	lexemes& prog_lex();
	/**
	 * checks if lexeme is in this input and sets l's offset into lr if true
	 * @param beg - +offset to the resulting range 
	 * @param l - lexeme
	 * @param lr - resulting range if lexeme found 
	 * @return true if lexeme found
	 */
	bool lexeme_pos(const size_t& beg, const lexeme& l, lexeme_range& lr) {
		if ((l[0] >= beg_ && l[0] < beg_ + size_)
		 || (l[1] >= beg_ && l[1] < beg_ + size_))
			return	lr[0] = l[0] - beg_ + beg,
				lr[1] = l[1] - beg_ + beg, true;
		return false;
	}
	/**
	 * returns next input or 0 if this is the last one in the fwd list
	 * @return next input
	 */
	input* next() { return next_.get(); }
	/**
	 * sets next input when this on is the last one and another one is added
	 * @param next input
	 */
	void set_next(std::unique_ptr<input> ni) { next_ = std::move(ni); }
	/**
	 * @return pointer to the beginning of the data
	 **/
	ccs begin() { return beg_; }
	/**
	 * @return current pointer to the data
	 **/
	ccs data() { return data_; }
	/**
	 * @return size of the input data
	 **/
	size_t size() { return size_; }
	/**
	 * sets offset of this input
	 * @param o offset
	 **/
	void set_offset(size_t o) { offset = o; }
	int_t get_int_t(ccs from, ccs to);
	void count_pos(ccs o, long& l, long& ch);
	bool parse_error(ccs offset, const char* err) {
		return parse_error(offset, err, offset);
	}
	bool parse_error(ccs offset, const char* err, ccs close_to);
	bool parse_error(ccs offset, const char* err, lexeme close_to);

	static std::string file_read(std::string fname);
	static std::string file_read_text(::FILE *f);
	static std::string file_read_text(std::string fname);
	static off_t fsize(const char *fname);
	static off_t fsize(ccs s, size_t len);
private:
	memory_map mm_;
	ccs beg_  = 0;
	ccs data_ = 0;
	size_t size_ = 0;
	bool allocated_ = false;
	int fd_ = -1;
	std::unique_ptr<input> next_ = 0;
	size_t load_stdin() {
		ostringstream_t ss; ss << CIN.rdbuf();
		beg_ = (ccs) strdup((ws2s(ss.str())).c_str()),
		data_ = beg_,
		allocated_ = true;
		return ss.str().size();
	}
};

class inputs { 
	friend class archive;
	std::unique_ptr<input> first_ = 0;
	struct input *last_ = 0;
	size_t size_ = 0;
public:
	void add(std::unique_ptr<input> in) {
		//COUT << "inputs size: " << size_ << " adding input: " << in.get() << " last: " << last_<< std::endl;
		input *inp = in.get();
		if (last_) last_->set_next(std::move(in));
		else first_ = std::move(in);
		last_ = inp;
		size_++;
	}
	input* add_stdin() {
		std::unique_ptr<input> in = std::make_unique<input>();
		input* ret = in.get();
		add(std::move(in));
		return ret;
	}
	input* add_file(std::string filename) {
		//COUT << "adding file input: " << filename << std::endl;
		std::unique_ptr<input> in = std::make_unique<input>(filename);
		input* ret = in.get();
		add(std::move(in));
		//COUT << "inputs size: " << size() << " this: " << this <<std::endl;
		return ret;
	}
	input* add_string(const string_t& str) {
		//COUT << "adding string input: " << to_string(str) << std::endl;
		std::unique_ptr<input> in =std::make_unique<input>(str.c_str());
		input* ret = in.get();
		add(std::move(in));
		//COUT << "inputs size: " << size() << " this: " << this <<std::endl;
		return ret;
	}
	input* add_string(const std::string& str) {
		//COUT << "adding string input: " << str << std::endl;
		std::unique_ptr<input> in = std::make_unique<input>(
			to_string_t(str).c_str());
		input* ret = in.get();
		add(std::move(in));
		//COUT << "inputs size: " << size() << " this: " << this <<std::endl;
		return ret;
	}
	input* first() const { return first_.get(); }
	input* last() const { return last_; }
	size_t size() const { return size_; }
	//is l in inputs? then point *in to the input and set l's offset into lr
	bool lexeme_pos(size_t& beg, const lexeme& l, input** in,
		lexeme_range& lr)
	{
		input* it = first_.get();
		while (it) {
			beg += sizeof(size_t) + 1;
			if (it->lexeme_pos(beg, l, lr)) return *in = it, true;
			beg += it->size() + 1;
			it = it->next();
		}
		return *in = 0, false;
	}
};

struct raw_form_tree;
typedef std::shared_ptr<raw_form_tree> sprawformtree;

struct raw_prog;

bool operator==(const lexeme& x, const lexeme& y);

static const std::set<std::string> str_bltins =
	{ "alpha", "alnum", "digit", "space", "printable", "count",
		"rnd", "print", "lprint", "halt", "fail",
		"bw_and", "bw_or", "bw_xor", "bw_not", "pw_add", "pw_mult"};

#define STR_TO_LEXEME(str) { (unsigned char *) (str), (unsigned char *) (str) + sizeof(str) - 1 }

struct elem {
	enum etype {
		NONE, SYM, NUM, CHR, VAR, OPENP, CLOSEP, ALT, STR,
		EQ, NEQ, LEQ, GT, LT, GEQ, BLTIN, NOT, AND, OR,
		FORALL, EXISTS, UNIQUE, IMPLIES, COIMPLIES, ARITH,
		OPENB, CLOSEB, OPENSB, CLOSESB,
	} type;
	t_arith_op arith_op = NOP;
	int_t num = 0;
	// The string that represents variants of this element.
	lexeme e{ 0, 0 };
	char32_t ch;
	elem() {}
	elem(int_t num) : type(NUM), num(num) {}
	elem(char32_t ch) : type(CHR), ch(ch) {}
	elem(etype type) : type(type) {
		switch(type) {
			case EQ: e = STR_TO_LEXEME("="); break;
			case OPENP: e = STR_TO_LEXEME("("); break;
			case CLOSEP: e = STR_TO_LEXEME(")"); break;
			case ALT: e = STR_TO_LEXEME("||"); break;
			case NEQ: e = STR_TO_LEXEME("!="); break;
			case LEQ: e = STR_TO_LEXEME("<="); break;
			case GT: e = STR_TO_LEXEME(">"); break;
			case LT: e = STR_TO_LEXEME("<"); break;
			case GEQ: e = STR_TO_LEXEME(">="); break;
			case NOT: e = STR_TO_LEXEME("~"); break;
			case AND: e = STR_TO_LEXEME("&&"); break;
			case FORALL: e = STR_TO_LEXEME("forall"); break;
			case EXISTS: e = STR_TO_LEXEME("exists"); break;
			case UNIQUE: e = STR_TO_LEXEME("unique"); break;
			case IMPLIES: e = STR_TO_LEXEME("->"); break;
			case COIMPLIES: e = STR_TO_LEXEME("<->"); break;
			case OPENB: e = STR_TO_LEXEME("{"); break;
			case CLOSEB: e = STR_TO_LEXEME("}"); break;
			case OPENSB: e = STR_TO_LEXEME("["); break;
			case CLOSESB: e = STR_TO_LEXEME("]"); break;
			default: assert(false); //should never reach here
		}
	}
	elem(etype type, lexeme e) : type(type), e(e) {
		DBG(assert(type!=NUM&&type!=CHR&&(type!=SYM||(e[0]&&e[1])));)
	}
	etype peek(input* in);
	bool is_paren() const { return type == OPENP || type == CLOSEP; }
	bool parse(input* in);
	bool operator<(const elem& t) const {
		if (type != t.type) return type < t.type;
		if (type == NUM) return num < t.num;
		if (type == CHR) return ch < t.ch;
		if (e[1]-e[0] != t.e[1]-t.e[0]) return e[1]-e[0]<t.e[1]-t.e[0];
		return strncmp(e[0], t.e[0], e[1]-e[0]) < 0;
	}
	bool operator==(const elem& t) const {
		if (type != t.type) return false;
		if (type == NUM) return num == t.num;
		if (type == CHR) return ch == t.ch;
		return e == t.e;
	}
	bool operator!=(const elem& t) const { return !(*this == t); }
	// Generate a fresh variable with respect to given dictionary.
	static elem fresh_var(dict_t &d) {
		return elem(elem::VAR, d.get_var_lexeme_from(d.get_fresh_var(0)));
	}
	// Generate a fresh symbol with respect to given dictionary.
	static elem fresh_sym(dict_t &d) {
		return elem(elem::SYM, d.get_sym(d.get_fresh_sym(0)));
	}
	std::string to_str() const{
		if (type == NUM) return to_string(to_string_t(num));
		if (type == CHR) return to_string(to_string_t(ch)); 
		return to_string(lexeme2str(e));			
	}
};

/* A raw term is produced from the parsing stage. In TML source code, it
 * takes the following form: <rel>(<arg1> <arg2> ... <argN>). A raw term can
 * occur in both heads and bodies. For example, rel(a(b(c)d e)f) is a raw
 * term with the following elements: 'rel', '(', 'a', '(', 'b', '(', 'c', 'd',
 * 'e', ')', 'f', ')'. Interpreting terms in this way keeps the universe's
 * size finite which in turn guarantees that TML programs terminate. */

struct raw_term {

	bool neg = false;
	enum rtextype { REL, EQ, LEQ, BLTIN, ARITH, CONSTRAINT } extype = raw_term::REL;

	//NOTE: we can add FORM1, FORM2 etc to rtextype
	// and replace t_arith_op by a form (once we do parse for compound arithmetic formulas)
	t_arith_op arith_op = NOP;
	// Elements of the raw term as described above.
	std::vector<elem> e;
	// A list formed from the raw-term's string by replacing opening parentheses
	// with -1s, closing parentheses with -2s, and contiguous sequences of elements
	// with their cardinality.
	ints arity;
	raw_term() {}
	raw_term(const elem &rel_name, const std::set<elem> &args) {
		e = { rel_name, elem(elem::OPENP) };
		for(const elem &a : args) {
			e.push_back(a);
		}
		e.push_back(elem(elem::CLOSEP));
		calc_arity(nullptr);
	}
	raw_term(const std::vector<elem> &f) : e(f) { calc_arity(nullptr); }
	raw_term(rtextype et, const std::vector<elem> &f) : extype(et), e(f) { calc_arity(nullptr); }
	bool parse(input* in, const raw_prog& prog, bool is_form = false,
		rtextype pref_type = raw_term::REL);
	bool calc_arity(input* in);
	void insert_parens(lexeme op, lexeme cl);
	void clear() { e.clear(), arity.clear(); }
	bool operator==(const raw_term& t) const {
		return neg == t.neg && e == t.e && arity == t.arity &&
			extype == t.extype;
			//iseq == t.iseq && isleq == t.isleq && islt == t.islt;
		//return neg == t.neg && e == t.e && arity == t.arity;
	}
	static raw_term _true() {
		return raw_term(raw_term::EQ, {elem(0), elem(elem::EQ), elem(0)});
	}
	static raw_term _false() {
		return raw_term(raw_term::EQ, {elem(0), elem(elem::EQ), elem(1)});
	}
	bool is_true() {
		return extype == raw_term::EQ && e.size() == 3 &&
			e[1].type == elem::EQ && e[0].type != elem::VAR &&
			e[2].type != elem::VAR && (e[0] == e[2]) != neg;
	}
	bool is_false() {
		return extype == raw_term::EQ && e.size() == 3 &&
			e[1].type == elem::EQ && e[0].type != elem::VAR &&
			e[2].type != elem::VAR && (e[0] != e[2]) != neg;
	}
};

struct macro {
	raw_term def;
	std::vector<raw_term> b;
	bool parse(input* in, const raw_prog& prog);
};

struct directive {
	elem rel;
	lexeme arg;
	raw_term t;
	int_t n;
	enum etype { STR, FNAME, CMDLINE, STDIN, STDOUT, TREE, TRACE, BWD }type;
	bool parse(input* in, const raw_prog& prog);
};

struct production {
//	bool start = false;
//	raw_term t;
	std::vector<elem> p;
	std::vector<raw_term> c{};   // constraints after production
	bool parse(input* in, const raw_prog& prog);
	bool operator<(const production& t) const { return p < t.p && c < t.c; }
	std::string to_str(size_t i=1 ){
		std::string ret;
		for( auto e = p.begin()+i; e != p.end(); e++)
			ret.append(e->to_str());			
		return ret;
	}
};

bool operator==(const std::vector<raw_term>& x, const std::vector<raw_term>& y);

struct raw_rule {
	std::vector<raw_term> h;
	// An empty b signifies the presence of a logical formula in prft if
	// prft != nullptr, otherwise it signifies that this rule is a fact.
	std::vector<std::vector<raw_term>> b;
	// Contains a tree representing the logical formula.
	mutable sprawformtree prft = nullptr;

	enum etype { NONE, GOAL, TREE };
	etype type = NONE;
	bool guarding = false;
	bool parse(input* in, const raw_prog& prog);
	void clear() { h.clear(), b.clear(), type = NONE; }
	raw_rule(){}
	raw_rule(etype type, const raw_term& t) : h({t}), type(type) {}
	raw_rule(const raw_term& t) : raw_rule(NONE, t) {}
	raw_rule(const raw_term& h, const raw_term& b) : h({h}), b({{b}}) {}
	raw_rule(const raw_term& h, const std::vector<raw_term>& _b) : h({h}) {
		if (!_b.empty()) b = {_b};
	}
	raw_rule(const raw_term& h, const std::vector<std::vector<raw_term>>& _b) : h({h}), b(_b) {}
	raw_rule(const std::vector<raw_term> &h,
			const std::vector<raw_term>& _b) : h(h) {
		if (!_b.empty()) b = {_b};
	}
	raw_rule(const raw_term& h, const sprawformtree &prft) : h({h}), prft(prft) {}
	// Clear b and set prft
	void set_prft(const sprawformtree &_prft) {
		prft = _prft;
		b.clear();
	}
	// Clear prft and set b
	void set_b(const std::vector<std::vector<raw_term>> &_b) {
		b = _b;
		prft = nullptr;
	}
	// If prft not set, convert b to prft, then return prft
	sprawformtree get_prft() const;
	// Return true iff b not empty or prft represents true
	bool is_b();
	// Returns b in an option type predicated on is_b
	std::optional<std::vector<std::vector<raw_term>>> get_b() {
		return is_b() ? std::optional<std::vector<std::vector<raw_term>>>(b) : std::nullopt;
	}
	inline bool is_form() { return prft.get(); }
	static raw_rule getdel(const raw_term& t) {
		raw_rule r(t, t);
		return r.h[0].neg = true, r;
	}
	bool operator==(const raw_rule& r) const {
		return h == r.h && b == r.b;
	}
	bool operator!=(const raw_rule& r) const { return !(*this == r); }
};

struct raw_prefix {
	elem qtype;
	elem ident;
	bool isfod = false;
	bool parse(input* in);
};

struct raw_form_tree {
	elem::etype type;
	raw_term *rt = nullptr; // elem::NONE is used to identify it
	elem * el = nullptr;

	sprawformtree l = nullptr;
	sprawformtree r = nullptr;
	bool neg = false;

	raw_form_tree (elem::etype _type, const raw_term &_rt) : type(_type), rt(new raw_term(_rt)) {}
	raw_form_tree (elem::etype _type, const elem &_el) : type(_type), el(new elem(_el)) {}
	raw_form_tree (elem::etype _type, sprawformtree _l = nullptr, sprawformtree _r = nullptr) : type(_type), l(_l), r(_r) {}
	raw_form_tree (elem::etype _type, const raw_term* _rt = NULL, const elem *_el =NULL,
		sprawformtree _l = NULL, sprawformtree _r = NULL)
	{
		type = _type;
		if(_rt) rt = new raw_term(*_rt);
		else rt = NULL;
		if(_el) el = new elem(*_el);
		else el = NULL;
		l = _l, r = _r;
	}
	~raw_form_tree() {
		if (rt) delete rt, rt = NULL;
		if (el) delete el, el = NULL;
	}
	void printTree(int level =0 );
	static sprawformtree simplify(sprawformtree &t);
};
struct raw_sof {
	const raw_prog& prog;
	raw_sof(const raw_prog& prog) :prog(prog) {}
private:
	bool parseform(input* in, sprawformtree &root, int precd= 0);
	bool parsematrix(input* in, sprawformtree &root);
public:
	bool parse(input* in, sprawformtree &root);
};

struct guard_statement {
	enum gtype { IF, WHILE } type;
	bool parse_condition(input* in, raw_prog& rp);
	bool parse_if(input* in, dict_t &dict, raw_prog& rp);
	bool parse_while(input* in, dict_t &dict, raw_prog& rp);
	bool parse(input* in, dict_t &dict, raw_prog& rp);
	sprawformtree prft;
	int_t id = 0;
	static int_t last_id;
};

struct raw_prog {
	enum ptype {
		PFP, LFP, GFP
	} type = PFP;
	std::vector<macro> vm;
	std::vector<directive> d;
	std::vector<production> g;
	std::vector<raw_rule> r;
	std::vector<guard_statement> gs;
	std::vector<raw_prog> nps;
	guard grd;

	std::set<lexeme, lexcmp> builtins;
//	int_t delrel = -1;

	int_t id = 0;
	static int_t last_id;

	raw_prog() { id = ++last_id; }

	bool parse(input* in, dict_t &dict);
	bool parse_statement(input* in, dict_t &dict, guard grd = {-1,false});
	bool parse_nested(input* in, dict_t &dict);
	bool parse_xfp(input* in, dict_t &dict);
	bool macro_expand(input *in , macro mm, const size_t i, const size_t j, 
				std::vector<raw_term> &vrt, dict_t &dict);
};

struct raw_progs {
	raw_prog p;
	raw_progs();
	bool parse(input* in, dict_t& dict);
};

bool throw_runtime_error(std::string err, std::string details = "");

bool parse_error(const char* o, const char* e, ccs s);
bool parse_error(const char* o, const char* e, lexeme l);
bool parse_error(ccs o, const char* e, std::string s);
bool parse_error(ccs o, const char* e);
bool parse_error(const char* e, lexeme l);
bool parse_error(const char* e);

template <typename T>
std::basic_ostream<T>& operator<<(std::basic_ostream<T>& os, const directive& d);
template <typename T>
std::basic_ostream<T>& operator<<(std::basic_ostream<T>& os, const elem& e);
template <typename T>
std::basic_ostream<T>& operator<<(std::basic_ostream<T>& os, const raw_form_tree &t);
template <typename T>
std::basic_ostream<T>& operator<<(std::basic_ostream<T>& os, const raw_term& t);
template <typename T>
std::basic_ostream<T>& operator<<(std::basic_ostream<T>& os, const sprawformtree prts);
template <typename T>
std::basic_ostream<T>& operator<<(std::basic_ostream<T>& os, const std::pair<raw_term, std::string>& p);
template <typename T>
std::basic_ostream<T>& operator<<(std::basic_ostream<T>& os, const raw_rule& r);
template <typename T>
std::basic_ostream<T>& operator<<(std::basic_ostream<T>& os, const raw_prog& p);
template <typename T>
std::basic_ostream<T>& operator<<(std::basic_ostream<T>& os, const raw_progs& p);
template <typename T>
std::basic_ostream<T>& operator<<(std::basic_ostream<T>& os, const production& p);
std::basic_ostream<char>& operator<<(std::basic_ostream<char>& os, const lexeme& l);
std::basic_ostream<wchar_t>& operator<<(std::basic_ostream<wchar_t>& os, const lexeme& l);

template <typename T>
std::basic_ostream<T>& print_raw_prog_tree(std::basic_ostream<T>& os,
	const raw_prog& p, size_t level);
template <typename T>
std::basic_ostream<T>& print_raw_rule(std::basic_ostream<T>& os,
	const raw_rule& r, size_t level);

bool operator==(const lexeme& l, std::string s);
bool operator==(const lexeme& l, const char* s);
bool operator<(const raw_term& x, const raw_term& y);
bool operator<(const raw_rule& x, const raw_rule& y);
void parser_test();


#endif
