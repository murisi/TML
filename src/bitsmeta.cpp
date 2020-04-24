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
#include <algorithm>
#include <list>
#include "bitsmeta.h"
#include "dict.h"
#include "input.h"
//#include "term.h"
//#include "output.h"
#include "err.h"
using namespace std;

// this is going away anyways, copy it for now, who cares
//#define mkchr(x) ((((int_t)x)<<2)|1)
//#define mknum(x) ((((int_t)x)<<2)|2)
//#define mksym(x) (int_t(x)<<2)
//#define un_mknum(x) (int_t(x)>>2)
#define mkchr(x) (int_t(x))
#define mknum(x) (int_t(x))
#define mksym(x) (int_t(x))
#define un_mknum(x) (int_t(x))

bool bitsmeta::BITS_FROM_LEFT = false;

void bitsmeta::init_type(primitive_type& type, const dict_t& dict) {
	switch (type.type) {
		case base_type::STR:
			// D: Q: TODO: how to set up individual arg's sym universe?
			// always init for STR/CHR or not? may alt universe size differ?
			if (type.bitness == 0) {
				type.set_bitness(BitScanR(dict.nsyms()));
				//type.bitness = BitScanR(dict.nsyms()); // nsyms-1? I guess
				// add extra because we haven't handled syms properly yet
				// i.e. we have 'shared dict universe' for all sym/str args
			}
			break;
		case base_type::CHR:
			// it's always 8, always init (or if correct it's 0)
			if (type.bitness == 0) {
				type.set_bitness(8);
				//type.bitness = 8;
			}
			break;
		case base_type::INT: 
			// calc bitness for ints (we just have num at this point).
			if (type.bitness == 0) {
				type.set_bitness(BitScanR(type.num));
				//type.bitness = BitScanR(type.num);
			}
			else if (type.num >= 1 << type.bitness) {
				o::dump() << L"bitsmeta: num > max(bits)..." << endl;
				type.set_bitness(BitScanR(type.num));
				//type.bitness = BitScanR(type.num);
			}
			break;
		case base_type::NONE:
			type.bitness = 1;
		default: ;
	}
}

/* prepare bits, bitness, caches if any */
void bitsmeta::init(const dict_t& dict) {
	// vargs should be set before entering, or rerun this on ordering change.
	if (types.empty()) return;
	mleftbits.clear();
	size_t lsum = 0, args = types.size(), maxb = 0;
	mleftbits[vargs[0]] = lsum;
	for (size_t i = 0; i != types.size(); ++i) {
		//arg_type& type = types[i]; // this is a bug
		arg_type& type = types[vargs[i]];
		// either branch or use an iterator similar to get_types()
		if (type.isPrimitive()) {
			init_type(type.primitive, dict);
		} else if (type.isCompound()) {
			//for (size_t it = 0; it != primitives.size(); ++it) {
			//	primitive_type& subtype = primitives[it];
			for(primitive_type& subtype : type.compound.types)
				init_type(subtype, dict);
		} else throw 0;
		//DBG(assert(type.get_bits() < 100););
		//if (vargs[i] == arg) break;
		if (i != args-1) {
			// we calc cache/maps regardless of the type, just need total bits
			// micro management is at the level of compound calls, eg leq_const
			lsum += types[vargs[i]].get_bits();
			mleftbits[vargs[i+1]] = lsum;
		}
		// vargs is redundant here as it's an aggregate, maxb/vbits will be same
		maxb = max(maxb, type.get_bits());
		//vbits[vargs[i]] = types[vargs[i]].get_bits();
	}
	args_bits = mleftbits.at(vargs[args-1]) + types[vargs[args-1]].get_bits();
	maxbits = maxb;

	size_t argsum = 0;
	if (maxbits == 0)
		return;
	mleftargs.clear();
	for (int_t bit = maxbits-1; bit >= 0; --bit) {
		map<size_t, size_t>& mpos = mleftargs[bit];
		for (size_t arg = 0; arg != types.size(); ++arg)
			if (types[vargs[arg]].get_bits() > size_t(bit))
				mpos[vargs[arg]] = argsum++;
	}
	DBG(assert(argsum == args_bits););
}

/* this's probably not necessary, just do init() when done w/ changes */
void bitsmeta::init_cache() {
	DBG(assert(!types.empty()););
	size_t args = types.size(), lsum = 0, maxb = 0, argsum = 0;
	mleftargs.clear();
	mleftbits.clear();
	mleftbits[vargs[0]] = lsum;
	// recalculate everything...
	for (size_t i = 0; i < args-1; ++i) { // process [0..args-2] (skip last)
		lsum += types[vargs[i]].get_bits();
		mleftbits[vargs[i+1]] = lsum;
		maxb = std::max(maxb, types[vargs[i]].get_bits());
		//vbits[vargs[i]] = types[vargs[i]].get_bits(); // wrong, missing args-1
	}
	args_bits = mleftbits.at(vargs[args-1]) + types[vargs[args-1]].get_bits();
	maxbits = std::max(maxb, types[vargs[args-1]].get_bits());
	DBG(assert(maxbits != 0);); // if (maxbits == 0) return;
	for (int_t bit = maxbits - 1; bit >= 0; --bit) {
		map<size_t, size_t>& mpos = mleftargs[bit];
		for (size_t arg = 0; arg != types.size(); ++arg)
			if (types[vargs[arg]].get_bits() > size_t(bit))
				mpos[vargs[arg]] = argsum++;
	}
	DBG(assert(argsum == args_bits););
}

/* 
 this effectively 'cements' the bits, any later on changes result in add_bits
 (it's done on tbl init/init_bits or later on permute_type/add_bit/add_bit_perm)
*/
void bitsmeta::init_bits() {
	vbits = uints(types.size());
	// TODO: easier is just vbits.push_back(types[i].get_bits());
	for (size_t i = 0; i != types.size(); ++i)
		// vargs is redundant here as it's an aggregate, maxb/vbits will be same
		vbits[vargs[i]] = types[vargs[i]].get_bits();
	bitsfixed = true;
}

bool bitsmeta::set_args(const ints& DBG(args), const argtypes& vtypes) {
	if (vtypes.empty()) return false;
	DBG(assert(vtypes.size() > 0);); // don't call this if nothing to do
	DBG(assert(args.size() == vtypes.size()););
	// we're empty initialized already (to table len), so sizes need to match
	DBG(assert(types.size() == vtypes.size()););
	// !nterms meaning we have no previous types / bits data (size's always >0)
	if (!nterms)
		types = vtypes;
	else
		for (size_t i = 0; i != types.size(); ++i)
			update_type(types[i], vtypes[i]);
	++nterms;
	return true;
}

bool bitsmeta::update_type(arg_type& type, const arg_type& newtype) {
	//if (type.kind != newtype.kind) return false;
	if (!type.isCompatible(newtype)) return false;
	if (newtype.isNone()) return false; // non-deterministic, can't help us
	if (type.isNone()) return type = newtype, true;
	// either branch or use an iterator similar to get_types()
	// newtype is a 'concrete' type (non-NONE), so test it instead of the type
	if (newtype.isPrimitive()) { // either both are primitive or NONE + prim.
		return update_type(type.primitive, newtype.primitive);
	}
	else if (newtype.isCompound()) {
		primtypes& types = type.compound.types;
		const primtypes& newtypes = newtype.compound.types;
		if (types.size() != newtypes.size()) {
			//throw 0;
			o::dump() << L"update_type: types.size() != newtypes.size()?"<<endl;
			return false;
		}
		bool changed = false;
		for (size_t i=0; i != types.size(); ++i)
			changed |= 
				update_type(types[i], newtypes[i]);
		return changed;
	} else throw 0;
}

bool bitsmeta::update_type(primitive_type& type, const primitive_type& newtype){
	bool changed = false;
	// if not set, skip
	if (newtype.isNone()) return false; //if (newtype.type == base_type::NONE)
	if (type.isNone()) { //if (type.type == base_type::NONE) {
		type = newtype;
		changed = true; // first init...
	}
	if (type.type != newtype.type) 
		parse_error(err_type, L""); //lexeme?
	//if (type.type == base_type::INT) 
	//	type.num = max(type.num, newtype.num); // no need if NONE but cheap
	if (type.type == base_type::INT && newtype.num > type.num) {
		//type.num = newtype.num;
		type.set_num(newtype.num);
		changed = true;
	}
	// we may not need this, it's 0 except for alt's (inheriting, once)
	if (newtype.bitness > type.bitness) {
		//type.bitness = newtype.bitness;
		type.set_bitness(newtype.bitness);
		changed = true;
	}
	return changed;
}

/* 
we're init already, this is just to update table back from alt/rules 
not entirely nice but handy to sync types in between tbls, rules, alts, for now
(this is to be deprecated, not much use, just use init() on any change)
*/
void bitsmeta::update_types(const argtypes& vtypes) {
	DBG(assert(types.size() <= vtypes.size()););
	bool changed = false;
	for (size_t i = 0; i != types.size(); ++i)
		changed |= 
			update_type(types[i], vtypes[i]);
	// this updates 'live', caches may change
	if (changed) init_cache();
}

bool bitsmeta::sync_types(
	argtypes& ltypes, const argtypes& rtypes, size_t larg, size_t rarg) {
	return sync_types(ltypes[larg], rtypes[rarg]);
}

bool bitsmeta::sync_types(arg_type& l, const arg_type& r) {
	//if (l.kind != r.kind) return false;
	if (!l.isCompatible(r)) return false;
	if (r.isNone()) return false; // non-deterministic, can't help us
	if (l.isNone()) return l = r, true;
	// either branch or use an iterator similar to get_types()
	// 'r' is a 'concrete' type (non-NONE), so test it instead of the type
	if (r.isPrimitive()) // either both are primitive or NONE + primitive
		return sync_types(l.primitive, r.primitive);
	else if (r.isCompound()) {
		primtypes& ltypes = l.compound.types;
		const primtypes& rtypes = r.compound.types;
		if (ltypes.size() != rtypes.size()) {
			//throw 0;
			o::dump() << L"sync_types: ltypes.size() != rtypes.size()??"<<endl;
			return false;
		}
		bool changed = false;
		for (size_t i = 0; i != ltypes.size(); ++i)
			changed |= sync_types(ltypes[i], rtypes[i]);
		return changed;
	}
	else throw 0;
}

bool bitsmeta::sync_types(primitive_type& l, const primitive_type& r)
{
	bool changed = false;
	bool lnone = l.isNone(), rnone = r.isNone();
	if (rnone) return false;
	else if (lnone) return l = r, true;
	if (l.type != r.type) parse_error(err_type, L"");
	if (l.type == base_type::INT && r.num > l.num) {
		//l.num = r.num;
		l.set_num(r.num);
		changed = true;
	}
	if (r.bitness > l.bitness) {
		//l.bitness = r.bitness;
		l.set_bitness(r.bitness);
		changed = true;
	}
	//DBG(assert(l.bitness < 100););
	//DBG(assert(r.bitness < 100););
	return changed;
}

bool bitsmeta::sync_types(arg_type& l, arg_type& r) {
	bool lchng, rchng;
	return sync_types(l, r, lchng, rchng);
}

bool bitsmeta::sync_types(arg_type& l, arg_type& r, bool& lchng, bool& rchng) {
	lchng = rchng = false;
	//if (l.kind != r.kind) return false;
	if (!l.isCompatible(r)) return false;

	bool lnone = l.isNone(), rnone = r.isNone();
	if (lnone && rnone) return false;
	else if (rnone) return r = l, rchng = true;
	else if (lnone) return l = r, lchng = true;

	// at this point, both are of same type (as are compatible + not NONE)
	if (l.isPrimitive())
		return sync_types(l.primitive, r.primitive, lchng, rchng);
	else if (l.isCompound()) {
		primtypes& ltypes = l.compound.types;
		primtypes& rtypes = r.compound.types;
		if (ltypes.size() != rtypes.size()) {
			//throw 0;
			o::dump() << L"sync_types: ltypes.size() != rtypes.size() ??"<<endl;
			return false;
		}
		bool changed = false;
		for (size_t i = 0; i != ltypes.size(); ++i) {
			bool lchanged, rchanged;
			changed |= 
				sync_types(ltypes[i], rtypes[i], lchanged, rchanged);
			lchng |= lchanged;
			rchng |= rchanged;
		}
		return changed;
	}
	else throw 0;
}

bool bitsmeta::sync_types(
	primitive_type& l, primitive_type& r, bool& lchng, bool& rchng)
{
	lchng = rchng = false;
	//bool changed = false;
	bool lnone = l.isNone(), rnone = r.isNone();
	if (lnone && rnone) return false;
	else if (rnone) return r = l, rchng = true;
	else if (lnone) return l = r, lchng = true;
	if (l.type != r.type) parse_error(err_type, L"");
	if (l.type == base_type::INT) {
		if (r.num > l.num) {
			//l.num = r.num;
			l.set_num(r.num);
			lchng = true;
		}
		else if (l.num > r.num) {
			//r.num = l.num;
			r.set_num(l.num);
			rchng = true;
		}
	}
	if (r.bitness > l.bitness) {
		//l.bitness = r.bitness;
		l.set_bitness(r.bitness);
		lchng = true;
	}
	else if (l.bitness > r.bitness) {
		//r.bitness = l.bitness;
		r.set_bitness(l.bitness);
		rchng = true;
	}
	//DBG(assert(l.bitness < 100););
	//DBG(assert(r.bitness < 100););
	return lchng || rchng;
}

bool bitsmeta::sync_types(argtypes& ltypes, argtypes& rtypes) {
	bool lchng, rchng;
	return sync_types(ltypes, rtypes, lchng, rchng);
}
bool bitsmeta::sync_types(
	argtypes& ltypes, argtypes& rtypes, bool& lchng, bool& rchng) {
	DBG(assert(ltypes.size() == rtypes.size()););
	//bool lchng = false, rchng = false;
	for (size_t i = 0; i != ltypes.size(); ++i) {
		bool lchanged, rchanged;
		sync_types(ltypes[i], rtypes[i], lchanged, rchanged);
		lchng |= lchanged;
		rchng |= rchanged;
	}
	// this updates 'live', caches may change
	//if (lchng) l.init_cache();
	//if (rchng) r.init_cache();
	return lchng || rchng;
}

bool bitsmeta::sync_types(argtypes& rtypes) {
	return sync_types(*this, rtypes);
}
bool bitsmeta::sync_types(bitsmeta& l, argtypes& rtypes) {
	bool lchng = false, rchng = false, changed;
	changed =
		sync_types(l.types, rtypes, lchng, rchng);
	if (lchng) l.init_cache();
	//if (rchng) r.init_cache();
	return changed; // lchng || rchng;
}

//bool bitsmeta::sync_types(bitsmeta& l, term& t) {
//	return sync_types(l, t.types);
//}

bool bitsmeta::sync_types(bitsmeta& l, bitsmeta& r) {
	bool lchng = false, rchng = false, changed;
	changed = 
		sync_types(l.types, r.types, lchng, rchng);
	if (lchng) l.init_cache();
	if (rchng) r.init_cache();
	return changed; // lchng || rchng;
}


