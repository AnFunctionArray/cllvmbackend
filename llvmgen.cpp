//#include "llvmgen.h"
//#include "llvm/IR/Instructions.h"
//#include "llvm/IR/Value.h"
//#include "llvm/Support/Allocator.h"
//#include "range/v3/view/reverse.hpp"

#include <range/v3/view/reverse.hpp>
#include "range/v3/view/single.hpp"
#include "llvm/TargetParser/Triple.h"
#include "llvm/IR/DebugLoc.h"
#include "llvm/IR/Metadata.h"
#include "llvm/IR/DebugInfo.h"
#include "llvm/IR/DIBuilder.h"
#include "llvm/BinaryFormat/Dwarf.h"
#include "llvm/IR/DebugInfoMetadata.h"
#ifdef _WIN32
#define _WSPIAPI_H_
#ifndef DEBUG_BACKEND
#define _ACRTIMP
#include <cassert>
#include <cstdio>
#undef assert
extern "C" __declspec(dllexport) void handler1(int sig);
extern "C" __declspec(dllimport) void __stdcall RaiseException(unsigned long dwExceptionCode, unsigned long dwExceptionFlags, unsigned long nNumberOfArguments, const unsigned long long* lpArguments);
extern "C" void __cdecl _wassert2(
	_In_z_ wchar_t const* _Message,
	_In_z_ wchar_t const* _File,
	_In_   unsigned       _Line
) {
	printf("%s\n - %s, %ud", _Message, _File, _Line);
	handler1(_Line);
	RaiseException(-1, 0, 0, nullptr);
}
#define _wassert _wassert2
#endif
#endif
#include "llvm/Support/raw_ostream.h"
#include "llvm/IR/GlobalAlias.h"
#include "llvm/Support/FileSystem.h"
#include "llvm/IR/AssemblyAnnotationWriter.h"
#include "llvm/Analysis/InstructionSimplify.h"
#include "llvm/ADT/ArrayRef.h"
#include "llvm/IR/Value.h"
#include <cctype>
#include <cstdlib>
#include <exception>
#include <iterator>
#include <array>
#include <bitset>
#include <cstddef>
#include <cstdint>
#include <functional>
#include <initializer_list>
#include <iostream>
#include <list>
#include <llvm/Bitcode/BitcodeWriter.h>
#include <llvm/IR/BasicBlock.h>
#include <llvm/IR/Constants.h>
#include <llvm/IR/DataLayout.h>
#include <llvm/IR/DerivedTypes.h>
#include <llvm/IR/Function.h>
#include <llvm/IR/GlobalIFunc.h>
#include <llvm/IR/GlobalVariable.h>
#include <llvm/IR/IRBuilder.h>
#include <llvm/IR/InstrTypes.h>
#include <llvm/IR/Instruction.h>
#include <llvm/IR/LLVMContext.h>
#include <llvm/IR/Module.h>
#include <llvm/IR/Type.h>
#include <llvm/Support/Error.h>
#include <llvm/Transforms/Utils/BasicBlockUtils.h>
#include <locale>
#include <ostream>
#include <queue>
#if 1//ndef __cpp_lib_ranges
#include <range/v3/algorithm/contains.hpp>
#include <range/v3/algorithm/find.hpp>
#include <range/v3/iterator/common_iterator.hpp>
#include <range/v3/iterator/concepts.hpp>
#include <range/v3/iterator/traits.hpp>
#include <range/v3/range/concepts.hpp>
#include <range/v3/range/traits.hpp>
#include <range/v3/view.hpp>
#include <range/v3/view/drop.hpp>
#include <range/v3/view/iota.hpp>
#include <range/v3/view/istream.hpp>
#define _Ranges ranges
#else
#define _Ranges std::ranges
#endif
#include <ranges>
#include <sstream>
#include <stdexcept>
#include <stdint.h>
#include <string>
#include <string_view>
#include <tuple>
#include <type_traits>
#include <unordered_set>
#include <vector>
#include <variant>
#include <unordered_map>
#include <fstream>
#include <deque>
//#include <source_location>
#include <algorithm>
//#include <oniguruma.h>
#include <llvm/ADT/Hashing.h>
#include <llvm/Support/FileSystem.h>
#include <latch>
#include <unordered_map>
#include <thread>
#include <condition_variable>
#include <optional>

#ifdef _WIN32
//#include <windows.h>
#endif

//#undef max

#ifndef __cpp_size_t_suffix
constexpr std::size_t operator "" zu(unsigned long long n)
{
	return n;
}

#endif

#define PCRE2_CODE_UNIT_WIDTH 8
#define PCRE2_STATIC

static std::string modname;

#if !defined(_WIN32) & !defined(_WIN64)
//#include <pcre2.h>
#else
//#include <pcre2/pcre2.h>
#endif

extern "C" {
#include "./main.h"
}

static bool allowccompat = true;

static bool allowdebug = false;

static bool pop_obtainvalbyidentifier_last();

DLL_EXPORT void endconstantexpr(), beginconstantexpr();

	static std::mutex boradcastingstrc;
	static std::mutex boradcastingscope;

DLL_EXPORT void insertinttoimm(const char* str, size_t szstr, const char* suffix, size_t szstr1, int type);

DLL_EXPORT void constructstring();

llvm::BranchInst* splitbb(const char* identifier, size_t szident);

struct var;
const llvm::fltSemantics& getfltsemfromtype(struct type flttype);

static llvm::IntegerType* (*getInt16Ty)(llvm::LLVMContext& C) = llvm::IntegerType::getInt16Ty;
static llvm::IntegerType* (*getInt32Ty)(llvm::LLVMContext& C) = llvm::IntegerType::getInt32Ty;
static llvm::IntegerType* (*getInt64Ty)(llvm::LLVMContext& C) = llvm::IntegerType::getInt64Ty;
static llvm::IntegerType* (*getInt128Ty)(llvm::LLVMContext& C) = llvm::IntegerType::getInt64Ty;

//static struct basehndl* phndl;

THREAD_LOCAL static std::list<std::list<var>> scopevar{ 1 };




static std::bitset<0xFFFF> scopevars_state;


THREAD_LOCAL std::list<std::list<var>> &scopevar_ = scopevar;


static std::list<std::list<var>> *_scopevar;

static std::mutex all;

static std::list<std::list<::var>> dummypar{1};

static std::list<::var> dummypar2{1};

const std::optional<std::list<struct var>::reverse_iterator> obtainvalbyidentifier(std::string ident, bool push = true, bool bfindtypedef = false, bool bcontinue = false);

extern const struct type basicint, basicsz();

enum class currdecltypeenum {
	STRUCTORUNION,
	TYPEDEF,
	CAST,
	PARAMS,
	NORMAL,
	UNKNOWN,
	NONE
};

//std::string currdeclspectypedef;

DLL_EXPORT
int
callstring(const char *fn, const char *what, size_t sizewhat);

DLL_EXPORT
int
callint(const char *fn, int n, const char *what, size_t sizewhat);

THREAD_LOCAL std::list<std::pair<std::list<std::string>, bool>> qualifsandtypes{ 1 };

THREAD_LOCAL static std::list<std::list<std::list<var>>> structorunionmembers{ 1 };

static std::unordered_map<unsigned int, std::unordered_map<unsigned int, std::list<var>>> structorunionmembers_global;

static std::list<std::list<std::list<var>>> *_structorunionmembers;

void startdeclaration(std::string typedefname);

struct currtypevectorbeingbuild_t {
	std::list<std::list<var>>::iterator p;
	currdecltypeenum currdecltype;

	decltype(p) endp;
};

THREAD_LOCAL std::list<currtypevectorbeingbuild_t> currtypevectorbeingbuild;

std::list<std::pair<std::array<llvm::BranchInst*, 2>, llvm::BasicBlock*>>::iterator startifstatement(bool pop);

THREAD_LOCAL static std::string currstring;

THREAD_LOCAL static bool bischarlit = false;

THREAD_LOCAL std::pair<std::string, std::string> currstruct;

THREAD_LOCAL std::string currenum;

bool bIsBasicFloat(const type& type);

bool bIsBasicInteger(const type& type);

typedef std::list<std::pair<std::array<llvm::BranchInst*, 2>, llvm::BasicBlock*>>::iterator arrtwovals;

struct branch {
	std::list<arrtwovals> first;
	std::list<struct var>::iterator iterval;
	std::list<arrtwovals>::iterator itersecond;
	std::list<std::array<llvm::BranchInst*, 2>> second;
};

THREAD_LOCAL std::list<branch> nbranches;

struct enumdef {
	std::string ident;
	std::list<std::list<struct var>::iterator > memberconstants;
	int maxcount{};
};

THREAD_LOCAL static std::list<std::string> callingconv;

DLL_EXPORT void endsizeofexpr();

THREAD_LOCAL std::list<std::list<enumdef>>  enums{ 1 };

std::list<std::list<enumdef>>  *_enums;

THREAD_LOCAL extern std::list<std::pair<std::list<std::string>, bool>> qualifsandtypes;

DLL_EXPORT unsigned constexpr stringhash(char const* input) {
	return *input ? static_cast<unsigned int> (*input) +
		33 * stringhash(input + 1)
		: 5381;
}

DLL_EXPORT void broadcast(unsigned thrid, unsigned pos);

void printtype(llvm::Type* ptype, std::string identifier) {
	std::string type_str;
	llvm::raw_string_ostream rso(type_str);
	ptype->print(rso);
	std::cout << identifier << " is " << rso.str() << std::endl;
}

constexpr inline auto operator"" _h(char const* p, size_t) {
	return stringhash(p);
}

THREAD_LOCAL static llvm::Module *mainmodule;

const char* datalayout_str = getenv("DATA_LAYOUT");

static THREAD_LOCAL llvm::DataLayout* pdatalayout;

llvm::Triple *ptriple;

bool bareweinabrupt(bool barewe = false);

THREAD_LOCAL static llvm::LLVMContext *llvmctx;

THREAD_LOCAL static llvm::IRBuilder<> *llvmbuilder;

THREAD_LOCAL static llvm::DIBuilder *llvmdibuilder;

THREAD_LOCAL static llvm::DICompileUnit *llvmcu;

THREAD_LOCAL static llvm::DISubprogram *llvmsub;

/*
0 - const
1 - restrict
2 - volatile
3 - israwtype
*/
typedef std::bitset<5> pointrtypequalifiers;

struct basic_type_origin {
	/*
		0 - last signed/unsigned or struct/union/enum
		1 - last basic type
		2 - deprecated - don't use - last storage specifier
		3 - last typedef or struct/union/enum name
	*/
	std::array<std::string, 4> basic;
	size_t longspecsn{}; //amount of long qualifiers
	std::bitset<4> qualifiers;

	bool operator==(const basic_type_origin&) const = default;

	std::shared_ptr<struct extra_basic_union> extra;
};

struct copy_assign_interf {
    copy_assign_interf() = default;
    copy_assign_interf(const copy_assign_interf&var) {
        var.morph_copy(this);
    }

	copy_assign_interf &operator=(const copy_assign_interf&var) {
        var.mutate(this);
        return *this;
    }

	virtual ~copy_assign_interf() = default;

    virtual void morph_copy(void *pobj) const {
        new (pobj) copy_assign_interf{};
    }

    virtual void mutate(void *pobj) const { }
};

struct annon_struc_mem : copy_assign_interf {
    ~annon_struc_mem() override = default;

    void morph_copy(void *pobj) const override {
        new (pobj) annon_struc_mem{};
        mutate(pobj);
    }

    void mutate(void *pobj) const override {
        reinterpret_cast<annon_struc_mem*>(pobj)->annonstruct = annonstruct;
    }

    std::list<::var> annonstruct;
};

struct extra_basic_union {
	extra_basic_union() {
        new (target_raw) copy_assign_interf{};
    }

    extra_basic_union(const extra_basic_union &var) {
        new (target_raw) copy_assign_interf{reinterpret_cast<const copy_assign_interf&>(var.target_raw)};
    }

    ~extra_basic_union() {
        reinterpret_cast<copy_assign_interf*>(target_raw)->~copy_assign_interf();
    }

    extra_basic_union &operator=(const extra_basic_union &var) {
        *reinterpret_cast<copy_assign_interf*>(target_raw) = reinterpret_cast<const copy_assign_interf&>(var.target_raw);
        return *this;
    }

	alignas(annon_struc_mem) std::byte target_raw[sizeof(annon_struc_mem)];
};

struct bascitypespec : basic_type_origin {
	void strip();


	bascitypespec& operator= (const bascitypespec& source) { // basic assignment
		basic_type_origin::operator=(source);
		//basic[2].clear();
		return *this;
	}

	operator std::string() {
		std::stringstream type;
		for (auto curr : basic)
			if(!curr.empty())
				type << curr << "_";
		type << "[[basic]]" << longspecsn;
		return type.str();
	}

	/*bool hasLinkage() {
		return _Ranges::contains(std::array{ "extern", "static" }, basic[2]);
	}*/

	bool operator== (const bascitypespec& comparer) {
		std::string ignoredmember = comparer.basic[2];
		auto ignoredqualifs = comparer.qualifiers;
		std::swap(ignoredmember, basic[2]);
		std::swap(ignoredqualifs, qualifiers);
		bool bareequal = basic_type_origin::operator==(comparer);
		basic[2] = ignoredmember;
		qualifiers = ignoredqualifs;
		return bareequal;
	}

	bool compareSign(const bascitypespec& comparer) {
		return _Ranges::contains(std::array{ "", "signed" }, comparer.basic[0]) &&
			_Ranges::contains(std::array{ "", "signed" }, basic[0]) ||
			comparer.basic[0] == basic[0];
	}
};

pointrtypequalifiers parsequalifiers(const std::string& qualifs) {
	pointrtypequalifiers ret;
	std::stringstream ssqualifs{ qualifs };
	std::string spec{};
	while (ssqualifs >> spec)
		switch (stringhash(spec.c_str())) {
		case "const"_h:
			ret[0] = 1;
			break;
		case "restrict"_h:
			ret[1] = 1;
			break;
		case "volatile"_h:
			ret[2] = 1;
			break;
		case "__ptr64"_h:
			ret[3] = 1;
			break;
		case "__ptr32"_h:
			ret[4] = 1;
			break;
		case "__stdcall"_h:
			callingconv.push_back(spec);
			break;
		default:
			std::cerr << "invalid specifier: " << spec << std::endl;
			std::terminate();
		}
	return ret;
}
struct var;

struct type {
	enum typetype {
		BASIC,
		POINTER,
		ARRAY,
		FUNCTION
	} uniontype;

	struct arrayinfo {
		uint64_t nelems;
		//std::bitset<1> qualifiers;
	};

	type(typetype a) : spec{ a }, uniontype{ a } {};
	struct functype {
		void strip();

		std::list<std::list<var>> parametertypes_list{ 1 };
		bool bisvariadic = false;
		std::string callconv;
	};

	type(const type& a) : spec{ a.uniontype }, uniontype{ a.uniontype } {
		*this = a;
	}

	~type() {
		std::array lambdas = {
			std::function{[&] { spec.basicdeclspec.~bascitypespec(); }},
			std::function{[&] { spec.ptrqualifiers.~bitset(); }},
			std::function{[&] {}},
			std::function{[&] { spec.func.~functype(); }} };
		lambdas[uniontype]();
	}

	type& operator= (const type& type) {

		if (type.uniontype != uniontype)
			this->~type(), new (this)::type{ type.uniontype };
		std::array lambdas = {
			std::function{
				[&] { cachedtype = type.cachedtype; spec.basicdeclspec = type.spec.basicdeclspec; }},
			std::function{
				[&] { cachedtype = type.cachedtype; spec.ptrqualifiers = type.spec.ptrqualifiers; }},
			std::function{[&] { spec.array = type.spec.array; }},
			std::function{[&] { cachedtype = type.cachedtype; spec.func = type.spec.func; }} };
		lambdas[uniontype]();

		return *this;
	}

	union typespec {
		typespec(typetype type) {
			std::array lambdas = {
				std::function{[&] { new (&basicdeclspec) bascitypespec{}; }},
				std::function{
					[&] { new (&ptrqualifiers) pointrtypequalifiers{}; }},
				std::function{[&] {}},
				std::function{[&] { new (&func) functype{}; }} };
			lambdas[type]();
		}
		~typespec() {}
		bascitypespec basicdeclspec;
		pointrtypequalifiers ptrqualifiers;
		arrayinfo array;
		functype func;
	} spec;

	void strip() {
		cachedtype = nullptr;

		std::array lambdas = {
			std::function{[&] { spec.basicdeclspec.strip(); }},
			std::function{[&] {}},
			std::function{[&] {}},
			std::function{[&] { spec.func.strip(); }} };
		lambdas[uniontype]();
	}

	llvm::Type* cachedtype{};
};

/*bool is_type_basic_void(const type& ty) {
	return ty.uniontype == type::BASIC && ty.spec.basicdeclspec.basic[1] == "void";
}

bool is_type_basic_void_or_ptr(const type& ty) {
	return ty.uniontype == type::BASIC && ty.spec.basicdeclspec.basic[1] == "void" || ty.uniontype == type::POINTER;
}*/

bool is_type_function_or_fnptr(std::list<type> tp) {
	return  (tp.front().uniontype == type::FUNCTION
		|| tp.front().uniontype == type::POINTER &&
		(++tp.begin())->uniontype == type::FUNCTION);
}

const ::type basicint = []() {
	::type tmp{ type::BASIC };
	tmp.spec.basicdeclspec.basic[1] = "int";
	return tmp;
}();

const ::type unsch = []() {
	::type tmp{ type::BASIC };
	tmp.spec.basicdeclspec.basic[0] = "unsigned";
	tmp.spec.basicdeclspec.basic[1] = "char";
	return tmp;
}();

const ::type nbitint = []() {
	::type tmp{ type::BASIC };
	tmp.spec.basicdeclspec.basic[1] = "[[nbitint]]";
	return tmp;
}();

const ::type basicsz() {
	::type tmp{ type::BASIC };
	if (pdatalayout->getPointerSizeInBits() == 64)
		tmp.spec.basicdeclspec.basic[1] = "long",
		tmp.spec.basicdeclspec.longspecsn = 1;
	else
		tmp.spec.basicdeclspec.basic[1] = "int"
		;
	return tmp;
};

const ::type basiclong = []() {
	::type tmp{ type::BASIC };
	tmp.spec.basicdeclspec.basic[0] = "unsigned";
	tmp.spec.basicdeclspec.basic[1] = "long";
	tmp.spec.basicdeclspec.longspecsn = 1;
	return tmp;
}();

llvm::Type* buildllvmtypefull(std::list<type>& decltypevector, bool ptrdeep = false);

llvm::Type* buildllvmtypefull(std::list<type>&& decltypevector) {
	return buildllvmtypefull(reinterpret_cast<std::list<type> &>(std::move(decltypevector)));
}

THREAD_LOCAL extern struct handlecnstexpr hndlcnstexpr;

THREAD_LOCAL extern struct handlefpexpr hndlfpexpr;

THREAD_LOCAL extern struct basehndl* phndl;

struct valbase {
	std::list<::type> type;
	union {
		llvm::Value* value{};
		llvm::Constant* constant;
	};
	std::string identifier{
#if 0
		"[[" + boost::stacktrace::to_string(boost::stacktrace::stacktrace()) + "]]"
#endif
	};

	auto requestType() {
		return buildllvmtypefull(type);
	}

	bool isconstant = (void*) & hndlcnstexpr == (void*)phndl;
};

typedef llvm::Value* lvaluebase;

struct val : valbase {
	lvaluebase lvalue{};

	void strip() {
		for(auto &elem : type) {
			elem.strip();
		}

		value = nullptr;
		constant = nullptr;
		lvalue = nullptr;
	}
};

val decay(val lvalue, bool bfunonly=false);


void addvar(var& lastvar, llvm::Constant* pInitializer = nullptr);

static THREAD_LOCAL std::list<llvm::BasicBlock*> pcurrblock;

struct var : valbase {

	llvm::Type* pllvmtype{};

	void seralise(bool doit=true) {
		if (doit) {
			strip();
		}
		else {
			if (type.front().spec.basicdeclspec.basic[1] == "enum") {
				constant = llvm::ConstantInt::get((*llvmctx), llvm::APInt(getInt32Ty(*llvmctx)->getBitWidth(), type.front().spec.basicdeclspec.longspecsn));
				type.front().spec.basicdeclspec.longspecsn = 0;

				type.front().spec.basicdeclspec.basic[1].clear();

				type.front().spec.basicdeclspec.basic[1] = "int";
			}
		}
	}

	void strip() {
		for(auto &elem : type) {
			elem.strip();
		}

		value = nullptr;
		constant = nullptr;
		pllvmtype = nullptr;
	}

	auto requestType() {
		fixupTypeIfNeededBase();
		return pllvmtype ? pllvmtype : 
			pllvmtype = buildllvmtypefull(type);
	}

	std::list<::type> fixupTypeIfNeededBase() {
		if(type.empty()) return type;
		auto& basicdeclspecarr = type.back().spec.basicdeclspec.basic;
		if (basicdeclspecarr[0].empty() && basicdeclspecarr[1].empty() && !basicdeclspecarr[3].empty()) {
			auto tmpident = identifier;
			identifier.clear();
			auto typedefval = obtainvalbyidentifier(basicdeclspecarr[3], false, true).value();
			type.pop_back();
			type.splice(type.end(), typedefval->fixupTypeIfNeededBase());
			identifier = tmpident;
		}
		return type;
	}
	llvm::Value* requestValue() {
		fixupTypeIfNeededBase();
		if ((value == nullptr)
			&& linkage != "typedef") {
			addvar(*this);
		}
		return value;
	}
	std::string linkage;

	llvm::BasicBlock* firstintroduced{ pcurrblock.empty() ? nullptr : pcurrblock.back() };
	
	bool ispotentiallywrong = false;
};

void parsebasictypenspecs(const std::list<std::string>& qualifs, ::var& outvar) {
	//bascitypespec ret;

	auto &ret = outvar.type.back().spec.basicdeclspec;

	for (const auto& a : qualifs)
		switch (stringhash(a.c_str())) {
		case "unsigned"_h:
		case "signed"_h:
			if (ret.basic[1].empty())
				ret.basic[1] = "int";
			ret.basic[0] = a;
			break;
		case "long"_h:
			ret.longspecsn++;
			ret.basic[1] = a;
			break;
		case "int"_h:
			if (ret.basic[1].empty())
				ret.basic[1] = a;
			break;
		//case "void"_h:
		case "_Bool"_h:
		case "short"_h:
		case "char"_h:
		case "float"_h:
		case "double"_h:
			ret.basic[1] = a;
			break;
		case "static"_h:
		case "extern"_h:
		case "auto"_h:
		case "typedef"_h:
			outvar.linkage = a;
			break;
		case "const"_h:
			ret.qualifiers[0] = 1;
			break;
		case "restrict"_h:
			ret.qualifiers[1] = 1;
			break;
		case "volatile"_h:
			ret.qualifiers[2] = 1;
			break;
		case "__stdcall"_h:
			callingconv.push_back(a);
			break;
		default:
			std::cerr << "invalid specifier: " << a << std::endl;
			std::terminate();
		}
}

void type::functype::strip() {
	for(auto &param : parametertypes_list.front()) {
		param.strip();
	}
}

void ::bascitypespec::strip()
{
	if (auto pannon = dynamic_cast<annon_struc_mem*>(reinterpret_cast<copy_assign_interf*>(extra->target_raw))) {
		for (auto &elem : pannon->annonstruct) {
			elem.strip();
		}
	}
}


uint64_t getConstantIntegerValue(const ::val &value) {
	return value.type.front().spec.basicdeclspec.basic[0] == "unsigned" ?
		llvm::dyn_cast<llvm::ConstantInt> (value.constant)->getZExtValue()
		:
		llvm::dyn_cast<llvm::ConstantInt> (value.constant)->getSExtValue();
}

THREAD_LOCAL static std::list<var> empty_func;

THREAD_LOCAL static std::list<var>::iterator currfunc = []() {
	empty_func.resize(1zu);
	return empty_func.begin();
}();

/*struct valueorconstant {
		template<class T> requires std::same_as<T, llvm::Value*> ||
std::same_as<T, llvm::Constant*> || std::same_as<T, void*> operator T()
		{
				return (T)p;
		}

		template<class T> requires std::same_as<T, llvm::Value*> ||
std::same_as<T, llvm::Constant*> || std::same_as<T, void*> valueorconstant&
operator=(T p)
		{
				this->p = p;
				return *this;
		}

		void* p;
};*/

THREAD_LOCAL static std::list<std::list<::val>::iterator> callees{};

llvm::Type* buildllvmtypefull(std::list<type>& decltypevector,
	std::list<type>* refdecltypevector);

val convertTo(val target, std::list<::type> to, bool bdecay=true);

/*auto gen_pointer_to_elem_if_ptr_to_array(llvm::Value* value,
	llvm::Type** p_type = nullptr) {
	llvm::Type* type_tmp,
		*& type = p_type
		? *p_type
		: (type_tmp = value->getType()->getPointerElementType());
	if (type->isArrayTy()) {
		type = type->getArrayElementType();
		value = llvmbuilder->CreatePointerCast(value, type->getPointerTo());
	}
	return value;
}*/

THREAD_LOCAL static std::list<val> immidiates{ 1 };

THREAD_LOCAL std::list<val> &immidiates_{ immidiates };

bool bIsBasicInteger(const type& type);

using ifstatiter = std::list<std::pair<std::array<llvm::BranchInst*, 2>, llvm::BasicBlock*>>::iterator;

struct opscopeinfo {
	std::list<val>::iterator immidiatesbegin;
	var currlogicopvar;

	ifstatiter lastifs;
	std::list<std::array<llvm::Value*, 2>> logicopswitches;
};

THREAD_LOCAL static std::list<opscopeinfo> opsscopeinfo;

using sub_range_ty = _Ranges::subrange<std::list<::type>::iterator>;

static ::type getequivalentfloattype(::type inweirdtype) {
	return inweirdtype.spec.basicdeclspec.basic[1] == "double" ? basiclong : basicsz();
}

struct basehndl /* : bindings_compiling*/ {
	//virtual llvm::Value* assigntwovalues() = 0;

	virtual void push_imm(std::optional<std::list<::var>::reverse_iterator> var) {
		extern void printvaltype(::val val);

		assert(var.has_value());

		val immidiate;


		llvm::Value* pglobal;

		immidiate.identifier = var.value()->identifier;

		pglobal = immidiate.value = var.value()->requestValue();

		immidiate.type = var.value()->type;

		printvaltype(immidiate);

		immidiate.lvalue = immidiate.value;

		if (immidiate.value && immidiate.type.front().uniontype != type::FUNCTION && !var.value()->isconstant)
			immidiate.value = llvmbuilder->CreateLoad(immidiate.requestType(), immidiate.value);

		phndl->immidiates.push_back(immidiate);

		printvaltype(immidiate);
	}

	virtual void constructstring() {
		std::list<::type> stirngtype{ 1, ::type::ARRAY };

		stirngtype.back().spec.array.nelems = currstring.size() + 1;

		stirngtype.push_back({ ::type::BASIC });

		stirngtype.back().spec.basicdeclspec.basic[1] = "char";

		auto lvalue = llvmbuilder->CreateGlobalStringPtr(
			currstring, "", 0);

		immidiates.push_back(
			val{ stirngtype, lvalue, "[[stringliteral]]" });
		auto& imm = immidiates.back();
		imm.lvalue = lvalue;
		imm.value = llvmbuilder->CreateLoad(imm.requestType(), imm.value);
	}

	virtual ::val create_val_tmp_aggregate(sub_range_ty iteratorty, _Ranges::subrange<std::list<::val>::iterator> immsiter) {

		::var tmp{ {{iteratorty.begin(), iteratorty.end()}, {}} };

		size_t imember = 0;

		std::vector<llvm::Value*> tmpimmidiates;

		if (tmp.type.front().uniontype == type::ARRAY)
			tmp.type.front().spec.array.nelems = std::max((uint64_t)std::distance(immsiter.begin(), immsiter.end()), iteratorty.front().spec.array.nelems) ;

		if(iteratorty.front().uniontype == type::BASIC) {
			if(iteratorty.front().spec.basicdeclspec.basic[0] != "struct")
			throw std::logic_error{"unsupported"};
		}

		tmp.requestValue();
		

		auto paggregatety = tmp.requestType();
		for (auto imm : immsiter) {
			auto member = llvmbuilder->CreateGEP(paggregatety, tmp.value, { llvmbuilder->getInt32(0), llvmbuilder->getInt32(imember++) });
			llvmbuilder->CreateStore(imm.value, member);
		}
		
		::val imm{tmp};

		imm.identifier = "[[initalizer_val_aggr]]";

		imm.lvalue = tmp.value;

		imm.value = llvmbuilder->CreateLoad(tmp.pllvmtype, tmp.value);

		//immidiates.insert(immsiter.end(), imm);
		immidiates.erase(immsiter.begin(), immsiter.end());
		return imm;
	}

	void adjus_aggregate_n_elems_if_needed() {
		auto last_imm = ::immidiates.back();

		auto& lastvar = currtypevectorbeingbuild.back().p->back();

		if (last_imm.type.front().uniontype == type::ARRAY) {
			if (lastvar.type.front().uniontype == type::ARRAY){
				lastvar.type.front().spec.array.nelems = last_imm.type.front().spec.array.nelems;

				lastvar.pllvmtype = nullptr;
			}
		}
	}

	virtual void init_end() {
		auto last_imm = ::immidiates.back();

		adjus_aggregate_n_elems_if_needed();

		::immidiates.pop_back();

		auto &lastvar = currtypevectorbeingbuild.back().p->back();

		lastvar.requestValue();

		obtainvalbyidentifier(lastvar.identifier);

		::immidiates.push_back(last_imm);

		phndl->assigntwovalues();
	}

	virtual val convertTo(val target, std::list<::type> to, bool bdecay=true) {
		extern val decay(val lvalue, bool bfunonly);
		extern bool comparetwotypesshallow(std::list<::type> one, std::list<::type> two);
		extern val coerceto(val target, std::list<::type> to);
		extern void printvaltype(val);
		target = decay(target, !bdecay);
		if (comparetwotypesshallow(target.type, to)) {
			target.type = to;
			return target;
		}
		printvaltype(target);
		printtype(buildllvmtypefull(to), "to");
		//if (to.front().spec.basicdeclspec.basic[3].empty())
		if (bIsBasicInteger(to.front()))
			if (bIsBasicInteger(target.type.front()))
				target.value = llvmbuilder->CreateIntCast(
					target.value, buildllvmtypefull(to),
					target.type.front().spec.basicdeclspec.basic[0] != "unsigned");
			else if (bIsBasicFloat(target.type.front()))
				if (to.back().spec.basicdeclspec.basic[0] == "unsigned")
					target.value = llvmbuilder->CreateFPToUI(target.value, buildllvmtypefull(to));
				else
					target.value = llvmbuilder->CreateFPToSI(target.value, buildllvmtypefull(to));
			else if (target.type.front().uniontype == type::POINTER)
				target.value = llvmbuilder->CreatePtrToInt(target.value, buildllvmtypefull(to));
			else {
				target = coerceto(target, to);
				to = target.type;
			}
		else if (bIsBasicFloat(to.front()))
			if (bIsBasicInteger(target.type.front()))
				if (target.type.back().spec.basicdeclspec.basic[0] == "unsigned")
					target.value = llvmbuilder->CreateUIToFP(target.value, buildllvmtypefull(to));
				else
					target.value = llvmbuilder->CreateSIToFP(target.value, buildllvmtypefull(to));
			else if (bIsBasicFloat(target.type.front()))
				target.value = llvmbuilder->CreateFPCast(
					target.value, buildllvmtypefull(to));
			else if (target.type.front().uniontype == type::POINTER) {
				target.value = llvmbuilder->CreatePtrToInt(target.value, buildllvmtypefull({ basicsz() }));
				target.value = llvmbuilder->CreateUIToFP(
						target.value, buildllvmtypefull(to));
			}
			else {
				target = coerceto(target, to);
				to = target.type;
			}
		else if (to.front().uniontype == type::POINTER)
			if (bIsBasicInteger(target.type.front()))
				target.value = llvmbuilder->CreateIntToPtr(target.value, buildllvmtypefull(to));
			else if (bIsBasicFloat(target.type.front()))
				target = coerceto(target, { basicsz() }),
				target.value = llvmbuilder->CreateIntToPtr(target.value, buildllvmtypefull(to));
			else if(target.type.front().uniontype == type::POINTER) {
				target.value = llvmbuilder->CreateBitCast(target.value, buildllvmtypefull(to));
			}
			else {
				target = coerceto(target, to);
				to = target.type;
			}
		else {
			//if (!bIsBasicFloat(target.type.front()) && !bIsBasicInteger(target.type.front())
			//	&& target.type.front().uniontype != type::POINTER) {
			target = coerceto(target, to);
			to = target.type;
			//}
			/*else {
				var tmp{ to };
				tmp.identifier = "[[coercetemporary]]";
				addvar(tmp);
				immidiates.push_back(val{ tmp });
				immidiates.back().type = target.type;
				immidiates.push_back(target);
				phndl->assigntwovalues();
				target = val{ tmp };
				immidiates.pop_back();
			}*/
		}

		target.type = to;

		return target;
	}

	virtual std::list<struct type> getdefaulttype() {
		return { basicint };
	}

	virtual void end_binary() {
		auto& currbranch = nbranches.back();

		var& ordinary = *currbranch.iterval;

		/*llvm::BranchInst* normalflow = nullptr;

		if (nbranches.back().first.size() > 1)
			normalflow = splitbb("", 0);*/

		val ordinary_imm = val{ (valbase)ordinary };

		//auto iternbranch = nbranches.begin();

		/*for (auto branch : nbranches.back().first | _Ranges::views::drop(1)) {
			//iternbranch = ++iternbranch;
			int fullindex = branch->first[0]->getSuccessor(1) != branch->second;
			branch->first[0]->setSuccessor(!fullindex, pcurrblock.back());
			branch->second->eraseFromParent();
			//ifstatements.erase(branch);

			ordinary_imm = ordinary;
			ordinary_imm.lvalues.push_back({ ordinary_imm.value, ordinary.type });

			immidiates.push_back(ordinary_imm);

			insertinttoimm((char*)branch->first[1], 1, "", 0, 3);

			phndl->assigntwovalues();

			immidiates.pop_back();

			branch->first[0] = splitbb("", 0);
		}*/

		llvm::BranchInst* lastsplit;

		if (!nbranches.back().second.empty()) {
			lastsplit = nbranches.back().second.back()[1];
			lastsplit->setSuccessor(0, pcurrblock.back());
			auto imm = immidiates.back();
			ordinary_imm.lvalue = ordinary_imm.value;
			immidiates.pop_back();
			immidiates.push_back(ordinary_imm);
			immidiates.push_back(imm);
			assigntwovalues();
			splitbb("", 0);
		}

		for (auto branch : nbranches.back().second)
			branch[0]->setSuccessor(0, pcurrblock.back());

		/*if (normalflow) {
			normalflow->setSuccessor(0, pcurrblock.back());*/
		if (!nbranches.back().second.empty()) {
			auto ordinaryval = ordinary.requestValue();
			ordinary_imm.value = llvmbuilder->CreateLoad(getInt32Ty((*llvmctx)), ordinaryval);

			immidiates.pop_back();

			immidiates.push_back(ordinary_imm);

		}
		//else //((llvm::AllocaInst*)ordinary.pValue)->replaceAllUsesWith(llvm::UndefValue::get(ordinary.pValue->getType())),
			//((llvm::AllocaInst*)ordinary.pValue)->eraseFromParent();
		//}

		scopevar.back().erase(currbranch.iterval);

		/**/

		nbranches.pop_back();
	}
	virtual void begin_branch() {
		auto& currbranch = nbranches.back();
		/*val ordinary_imm = *currbranch.iterval;
		auto imm = immidiates.back();
		ordinary_imm.lvalues.push_back({ ordinary_imm.value, currbranch.iterval->type });
		immidiates.pop_back();
		immidiates.push_back(ordinary_imm);
		immidiates.push_back(imm);
		phndl->assigntwovalues();*/
		currbranch.first.insert(++currbranch.first.begin(), startifstatement(false));
		//currbranch.second.push_back(currbranch.first.back());
		//ordinary_imm.value = llvmbuilder->CreateLoad(ordinary_imm.value);
		//immidiates.push_back(ordinary_imm);
	}
	virtual void begin_binary() {
		var ordinary;
		ordinary.type = { basicint };
		scopevar.back().push_back(ordinary);
		scopevar.back().back().requestValue();
		nbranches.push_back({ std::list<arrtwovals>{1}, --scopevar.back().end() });
		nbranches.back().itersecond = nbranches.back().first.begin();

		/*val ordinary_imm = scopevar.back().back();
		ordinary_imm.lvalues.push_back({ ordinary_imm.value, ordinary.type });

		immidiates.push_back(ordinary_imm);

		insertinttoimm("1", sizeof "1" - 1, "", 0, 3);

		assigntwovalues();

		immidiates.pop_back();*/
	}

	thread_local static std::list<val>& immidiates;

	virtual basehndl* (*getrestorefn())(basehndl*) {
		return [](basehndl* pnhdl) -> basehndl* {
			return new (pnhdl) basehndl{};
		};
	}
	//friend void beginlogicalop(int blastorfirst);
	virtual llvm::Value* CreateCastInst(llvm::Value* C, llvm::Type* Ty, bool bissigned) {
		return llvmbuilder->CreateIntCast(C, Ty, bissigned);
	}

	virtual llvm::Constant* getValZero(val val) {
		llvm::APInt apint{};

		if (bIsBasicInteger(val.type.front()))
			apint = llvm::APInt{ dyn_cast<llvm::IntegerType> (val.value->getType())->getBitWidth(), 0 };

		return llvm::ConstantInt::getIntegerValue(val.value->getType(), apint);
	}

	using val = ::val;

	virtual void getpositive() {
		immidiates.back() = integralpromotions(immidiates.back());
	}

	virtual void getnegative() {
		immidiates.back() = integralpromotions(immidiates.back());

		immidiates.back().value = llvmbuilder->CreateNeg(immidiates.back().value);
	}

	virtual void getbitwisenot() {
		immidiates.back() = integralpromotions(immidiates.back());

		immidiates.back().value = llvmbuilder->CreateNot(immidiates.back().value);
	}

	virtual llvm::Value* getlogicalnot() {
		extern ::val decay(::val lvalue);

		auto& op = immidiates.back();

		llvm::Value* originstr;

		extern void printvaltype(val);

		printvaltype(op);

		if (std::list listtp = { type{type::BASIC} }; listtp.back().spec.basicdeclspec.basic[1] = "int", true)
			op = convertTo(op, listtp);

		originstr = op.value = llvmbuilder->CreateICmp(
			llvm::CmpInst::Predicate::ICMP_EQ, op.value,
			getValZero(op));
		op.type.erase(op.type.begin(), --op.type.end());

		op.value = CreateCastInst(op.value, getInt32Ty((*llvmctx)), false);

		extern void printvaltype(::val val);

		printvaltype(op);

		op.type.back().spec.basicdeclspec.basic[1] = "int",
			op.type.back().spec.basicdeclspec.basic[0] = "";

		return originstr;
	}

	val integralpromotions(val in) {

		if(!bIsBasicFloat(in.type.front()) && !bIsBasicInteger(in.type.front())) {
			if(in.type.front().uniontype != type::POINTER && in.type.front().uniontype != type::FUNCTION) {
				std::list type = { nbitint };
				type.front().spec.basicdeclspec.longspecsn = pdatalayout->getTypeSizeInBits(in.requestType());
				in = convertTo(in, type, false);
			}
			else {
				in = convertTo(in, { basicsz() });
			}
		}
		if (allowccompat) {
			assert(in.type.size() == 1);

			std::cout << "promoting" << std::endl;

			extern void printvaltype(val);

			printvaltype(in);

			switch (
				stringhash(in.type.back().spec.basicdeclspec.basic[1].c_str())) {
			case "char"_h:
			case "short"_h:
				switch (stringhash(
					in.type.back().spec.basicdeclspec.basic[0].c_str())) {
				default:
				case "signed"_h:
					in.value =
						CreateCastInst(in.value, getInt32Ty((*llvmctx)), true);
					break;
				case "unsigned"_h:
					in.value =
						CreateCastInst(in.value, getInt32Ty((*llvmctx)), false);
					break;
				}
				in.type.back().spec.basicdeclspec.basic[0] = "";
				in.type.back().spec.basicdeclspec.basic[1] = "int";
			}
		}
		return in;
	}

	/*static int getrank(::type basictyp) {
		switch (stringhash(basictyp.spec.basicdeclspec.basic[0].c_str())) {
		default:
		case "signed"_h:
		case "unsigned"_h:
			switch (stringhash(basictyp.spec.basicdeclspec.basic[1].c_str())) {
			case "char"_h:
				return 0;
			case "short"_h:
				return 1;
			case "int"_h:
			case "long"_h:
				return 2 + basictyp.spec.basicdeclspec.longspecsn;
			case "__int64"_h:
				return 4;
			}
		}

		throw std::out_of_range{ "not a integer" };
	}*/

	std::array<val, 2> usualarithmeticconversions(std::array<val, 2> ops_in) {

		for (auto i = 0; i < 2; ++i)
			if (!bIsBasicFloat(ops_in[i].type.front()) && !bIsBasicInteger(ops_in[i].type.front())) {
				if(ops_in[i].type.front().uniontype != type::POINTER && ops_in[i].type.front().uniontype != type::FUNCTION) {
					if (!bIsBasicFloat(ops_in[!i].type.front())) {
						std::list type = { nbitint };
						type.front().spec.basicdeclspec.longspecsn = std::max(pdatalayout->getTypeSizeInBits(ops_in[i].requestType()), pdatalayout->getTypeSizeInBits(ops_in[!i].requestType()));
						ops_in[i] = convertTo(ops_in[i], type, false);
					}
					else {
						ops_in[i] = convertTo(ops_in[i], ops_in[!i].type, false);
					}
				}
				else
					ops_in[i] = convertTo(ops_in[i], { basicsz() });
			}

		std::array ops = { &ops_in[0], &ops_in[1] };

		std::array refspecops = { &ops[0]->type.back().spec.basicdeclspec, &ops[1]->type.back().spec.basicdeclspec };

		extern void printvaltype(val);

		printvaltype(*ops[0]);

		printvaltype(*ops[1]);

		for (auto i = 0; i < 2; ++i)
			if (std::list listtp = { type{type::BASIC} };
				listtp.back().spec.basicdeclspec.basic[0] = "unsigned",
				listtp.back().spec.basicdeclspec.basic[1] = "long",
				listtp.back().spec.basicdeclspec.longspecsn = 1,
				ops[i]->type.size() > 1)
				ops_in[i] = convertTo(*ops[!i], listtp);
			else if (_Ranges::contains(std::array{ "double", "float" }, refspecops[i]->basic[1])) {
				if(refspecops[!i]->basic[1] == "double") {
					ops_in[i] = convertTo(*ops[i], ops[!i]->type);
					return ops_in;
				}
				for (ops_in[!i] = convertTo(*ops[!i], ops[i]->type);;)
					return ops_in;
			}

		ops_in[0] = integralpromotions(*ops[0]);

		ops_in[1] = integralpromotions(*ops[1]);

		refspecops = { &ops[0]->type.back().spec.basicdeclspec, &ops[1]->type.back().spec.basicdeclspec };

		if (*refspecops[0] == *refspecops[1])
			return ops_in;

		/*if (getrank(ops[0]->type.back()) < getrank(ops[1]->type.back()))
			std::swap(ops[0], ops[1]), std::swap(refspecops[0], refspecops[1]);*/

		//If same sign just convert to the higher rank

		if (refspecops[0]->compareSign(*refspecops[1])) {

			if (pdatalayout->getTypeSizeInBits(ops[1]->value->getType()) 
				> pdatalayout->getTypeSizeInBits(ops[0]->value->getType()))
				std::swap(ops[0], ops[1]), std::swap(refspecops[0], refspecops[1]);

			ops[1]->value = CreateCastInst(ops[1]->value, ops[0]->value->getType(), refspecops[1]->basic[0] != "unsigned");

			*refspecops[1] = *refspecops[0];

			return ops_in;
		}

		if (refspecops[0]->basic[0] != "unsigned") {
			std::swap(ops[0], ops[1]), std::swap(refspecops[0], refspecops[1]);
		}

		if (pdatalayout->getTypeSizeInBits(ops[1]->value->getType()) 
			> pdatalayout->getTypeSizeInBits(ops[0]->value->getType()))
		//If the signed type can represent all the bits of the unsigned convert to it
		{
			ops[0]->value = CreateCastInst(ops[0]->value, ops[1]->value->getType(), false);

			*refspecops[0] = *refspecops[1];
		}
		//else convert to the unsigned one
		else {
			ops[1]->value = CreateCastInst(ops[1]->value, ops[0]->value->getType(), true);

			*refspecops[1] = *refspecops[0];
		}

		return ops_in;
	}

	auto &requireint(::val &op) {
		if (!bIsBasicInteger(op.type.front()) ) {
			extern val coerceto(val target, std::list<::type> to);
			if(op.type.front().uniontype != type::FUNCTION && op.type.front().uniontype != type::POINTER
				&& !bIsBasicFloat(op.type.front())) {
				std::list type = { nbitint };
				type.front().spec.basicdeclspec.longspecsn = pdatalayout->getTypeSizeInBits(op.requestType());
				op = convertTo(op, type, false);
			}
			else
				op = convertTo(op, { basicsz() });
		}
		return op;
	}

	auto getops(bool busual = true, bool bassign = false, bool requireint=false) {

		auto ops = std::array{ *(----immidiates.end()), immidiates.back() };

		if(requireint) {
			ops[0] = this->requireint(ops[0]);
			ops[1] = this->requireint(ops[1]);
		}

		//auto op0type = ops[0].value->getType();

		//if (!bassign)
		//ops[0] = integralpromotions(ops[0]);

		//if (ops[1].type.front().uniontype == type::BASIC)
		//ops[1] = integralpromotions(ops[1]);

		//ops[0].value =
		//	/*gen_pointer_to_elem_if_ptr_to_array*/ (ops[0].value);

		/*if (busual)
			ops = usualarithmeticconversions(ops);
		else if (ops[1].type.front().uniontype == type::BASIC &&
			op0type != ops[1].value->getType())
			ops[1].type = ops[0].type,
			ops[1].value = llvmbuilder->CreateIntCast(
				ops[1].value, op0type,
				ops[0].type.back().spec.basicdeclspec.basic[0] != "unsigned");*/

		if (busual)
			ops = usualarithmeticconversions(ops);

		immidiates.erase(----immidiates.end(), immidiates.end());

		return ops;
	}

	virtual void mlutiplylasttwovalues() {
		std::array ops = getops();

		ops[0].value = llvmbuilder->CreateMul(ops[0].value, ops[1].value);

		immidiates.push_back(ops[0]);
	}

	virtual void dividelasttwovalues() {
		std::array ops = getops();

		if (ops[0].type.back().spec.basicdeclspec.basic[0] != "unsigned")
			ops[0].value = llvmbuilder->CreateSDiv(ops[0].value, ops[1].value);
		else
			ops[0].value = llvmbuilder->CreateUDiv(ops[0].value, ops[1].value);

		immidiates.push_back(ops[0]);
	}

	virtual void modulolasttwovalues() {
		std::array ops = getops();

		if (ops[0].type.back().spec.basicdeclspec.basic[0] != "unsigned")
			ops[0].value = llvmbuilder->CreateSRem(ops[0].value, ops[1].value);
		else
			ops[0].value = llvmbuilder->CreateURem(ops[0].value, ops[1].value);

		immidiates.push_back(ops[0]);
	}

	virtual void addlasttwovalues(bool bminus, bool busual = true) {
		extern ::val decay(::val lvalue);

		if (subscripttwovalues(bminus)) {
			getaddress();
			return;
		}
		std::array ops = std::array{ *(----immidiates.end()), immidiates.back() };

		immidiates.erase(----immidiates.end(), immidiates.end());

		//ops[0] = decay(ops[0]);

		//ops[1] = decay(ops[1]);

		extern void printvaltype(val);

		busual && (ops = usualarithmeticconversions(ops), 0),
			printvaltype(ops[0]),
			printvaltype(ops[1]),
			ops[0].value = llvmbuilder->CreateAdd(
				ops[0].value,
				!bminus ? ops[1].value : llvmbuilder->CreateNeg(ops[1].value));

		immidiates.push_back(ops[0]);
	}

	virtual void shifttwovalues(bool bright) {
		std::array ops = getops(false);

		ops[0] = requireint(ops[0]);

		ops[0] = integralpromotions(ops[0]);

		ops[1] = requireint(ops[1]);

		/*if(bIsBasicFloat(ops[0].type.front())) {
			std::list<::type> longty = { basicint };

			if(ops[0].type.front().spec.basicdeclspec.basic[1] == "double") {

				longty.back().spec.basicdeclspec.longspecsn = 2;
			}

			ops[0] = convertTo(ops[0], longty);
		}

		ops[1] = convertTo(ops[1], ops[0].type);*/

		ops[1].value = llvmbuilder->CreateIntCast(ops[1].value, ops[0].value->getType(), false);

		if (!bright)
			ops[0].value = llvmbuilder->CreateShl(ops[0].value, ops[1].value);
		else if (ops[0].type.back().spec.basicdeclspec.basic[0] != "unsigned")
			ops[0].value = llvmbuilder->CreateAShr(ops[0].value, ops[1].value);
		else
			ops[0].value = llvmbuilder->CreateLShr(ops[0].value, ops[1].value);

		immidiates.push_back(ops[0]);
	}

	virtual void relatetwovalues(llvm::CmpInst::Predicate pred, llvm::CmpInst::Predicate unsignedpred, llvm::CmpInst::Predicate fltpred) {
		std::array ops = getops();

		if (ops[0].type.back().spec.basicdeclspec.basic[0] != "unsigned")
			ops[0].value =
			llvmbuilder->CreateICmp(pred, ops[0].value, ops[1].value);
		else
			ops[0].value =
			llvmbuilder->CreateICmp(unsignedpred, ops[0].value, ops[1].value);

		ops[0].value =
			CreateCastInst(ops[0].value, getInt32Ty((*llvmctx)), false);

		ops[0].type.erase(ops[0].type.begin(), --ops[0].type.end());
		;

		ops[0].type.back().spec.basicdeclspec.basic[1] = "int",
			ops[0].type.back().spec.basicdeclspec.basic[0] = "";

		immidiates.push_back(ops[0]);
	}

	virtual void bitwisetwovalues(llvm::Instruction::BinaryOps op) {
		std::array ops = getops(true, false, true);

		ops[0].value = llvmbuilder->CreateBinOp(op, ops[0].value, ops[1].value);

		immidiates.push_back(ops[0]);
	}

	virtual void logictwovalues(bool bisand) {

		std::array ops = getops(false);

		ops[0].value = llvmbuilder->CreateICmp(
			llvm::CmpInst::Predicate::ICMP_NE, ops[0].value, getValZero(ops[0]));

		ops[1].value = llvmbuilder->CreateICmp(
			llvm::CmpInst::Predicate::ICMP_NE, ops[1].value, getValZero(ops[1]));

		//if (bisand != 2)

		ops[0].value = !bisand
			? llvmbuilder->CreateOr(ops[0].value, ops[1].value)
			: llvmbuilder->CreateAnd(ops[0].value, ops[1].value);
		//else
		//	instr[0] = ops[0].value = llvmbuilder->CreateOr(ops[0].value, ops[1].value),
		//	instr[1] = ops[0].value = llvmbuilder->CreateAnd(ops[0].value, ops[1].value);

		ops[0].value = llvm::CastInst::Create(
			llvm::Instruction::CastOps::ZExt, ops[0].value,
			getInt32Ty((*llvmctx)), "", pcurrblock.back());

		ops[0].type.erase(ops[0].type.begin(), --ops[0].type.end());

		ops[0].type.back().spec.basicdeclspec.basic[1] = "int",
			ops[0].type.back().spec.basicdeclspec.basic[0] = "";

		immidiates.push_back(ops[0]);
	}

	virtual llvm::Value* assigntwovalues() {
		std::array ops = getops(false, true);

		extern ::val decay(::val lvalue);

		llvm::Value* instr;

		::var lastvar;

		if (ops[0].type.front().uniontype == type::FUNCTION) {
			if (auto itervar = obtainvalbyidentifier(ops[0].identifier, false); !itervar.has_value() || itervar.value()->ispotentiallywrong) {
				::var newvar{ {.identifier = ops[0].identifier} };
				newvar.type = newvar.type = { basicint };
				newvar.firstintroduced = nullptr;
				newvar.ispotentiallywrong = true;

				if(itervar.has_value()) {
					lastvar = std::move(**itervar);

					assert(pop_obtainvalbyidentifier_last());
				}

				scopevar.front().push_back(newvar);

				addvar(scopevar.front().back());

				obtainvalbyidentifier(newvar.identifier);

				ops[0] = immidiates.back();
				
				immidiates.pop_back();

				if(lastvar.value) {
					std::cout << "not found: " << ops[0].identifier << " patching up as object" << std::endl;

					lastvar.value->replaceAllUsesWith(obtainvalbyidentifier(newvar.identifier, false).value()->value);
				}
			}
			else {
				printf("Warning - no op: %s\n", ops[0].identifier.c_str());
				immidiates.push_back(ops[1]);
				return ops[1].value;
			}
		}

		ops[1] = convertTo(ops[1], ops[0].type, ops[0].type.front().uniontype == type::POINTER && ops[1].lvalue);

		printtype(ops[0].lvalue->getType(),
			ops[0].identifier);
		printtype(ops[1].value->getType(), ops[1].identifier);

		instr = llvmbuilder->CreateStore(ops[1].value, ops[0].lvalue);

		immidiates.push_back(val{ {ops[1].type, ops[1].value, ""}, ops[1].lvalue });

		return instr;
	}

	virtual bool subscripttwovalues(bool bminus = false) {

		auto ops = std::array{ *(----immidiates.end()), immidiates.back() };

		for (auto i = 0; i < 2; ++i)
			if (ops[i].type.front().uniontype == type::POINTER ||
				ops[i].type.front().uniontype == type::ARRAY)
				if (ops[!i].type.front().uniontype == type::BASIC) {
					ops[!i] = requireint(ops[!i]);

					immidiates.erase(----immidiates.end(), immidiates.end());
					bool isarray = ops[i].type.front().uniontype == type::ARRAY;
					auto& targetplain = ops[i];
					llvm::Type* targettype = buildllvmtypefull(targetplain.type, true);
					llvm::Value* target = isarray ? targetplain.lvalue : targetplain.value;
					std::vector<llvm::Value*> gepinidces{ ops[!i].value };

					ops[i].type.erase(ops[i].type.begin());

					gepinidces.insert(gepinidces.begin(), dyn_cast<llvm::Value>(llvmbuilder->getInt32(0)));

					if (!isarray)
						targettype = llvm::ArrayType::get(ops[i].type.front().cachedtype, 0);
					
					assert(!targettype->isFunctionTy());

					ops[!i].value = !bminus
						? ops[!i].value
						: llvmbuilder->CreateNeg(ops[!i].value);
					llvm::Value* lvalue = llvmbuilder->CreateGEP(
						targettype, target,
						gepinidces);
					immidiates.push_back(
						val{ {ops[i].type, ops[i].type.front().uniontype != type::FUNCTION
							 ? llvmbuilder->CreateLoad(ops[i].type.front().cachedtype, lvalue)
							 : lvalue,
						 ops[i].identifier}, lvalue });
					printtype(lvalue->getType(), ops[i].identifier);
					printtype(immidiates.back().value->getType(),
						ops[i].identifier);
					printtype(ops[!i].value->getType(), ops[!i].identifier);
					return true;
				}
		return false;
	}

	virtual void getaddress() {
		extern void printvaltype(val);
		auto& val = immidiates.back();
		val.value = val.lvalue;
		val.type.insert(val.type.begin(), { type::POINTER });
		printvaltype(val);
		//val.lvalue->unloadgep();
	}

	virtual void applyindirection() {

		unsigned int type = 3; // << 2 | 2;

		auto immlvalue = immidiates.back();

		std::cout << "applying indirection" << std::endl;

		insertinttoimm("0", sizeof "0" - 1, "ul", sizeof "ul" - 1, type);

		extern val coerceto(val target, std::list<::type> to);

		if (!subscripttwovalues()) {
			auto& imm = *----immidiates.end();
			imm = coerceto(imm, { type::POINTER, basicint });
			subscripttwovalues();
		}
	}

	void insertinttoimm(const char* str, size_t szstr, const char* suffix_in, size_t szstr1, int type) {
		std::string imm, suffix{ suffix_in, szstr1 };

		imm.assign(str, szstr);

		std::list<::type> currtype = { 1, ::type::BASIC };

		const bool isunsigned = suffix.find("u") != suffix.npos || suffix.find("U") != suffix.npos;

		const bool islonglong = suffix.find("ll") != suffix.npos || suffix.find("LL") != suffix.npos;

		const bool islong = !islonglong && (suffix.find("l") != suffix.npos || suffix.find("L") != suffix.npos);

		//type >>= 2;

		"testing some stuff";

		(long long)( ~(1ULL << sizeof(long long) * 8 - 1) &  ~(LLONG_MIN >> sizeof(long long) * 8 - 16));

		(unsigned long long)(~(LLONG_MIN >> sizeof(long long) * 8 - 33) );

		"end testing";

		const int base[] = { 16, 2, 7, 10 };

		const unsigned long long val = isunsigned ? std::stoull(imm, nullptr, base[type]) : std::stoll(imm, nullptr, base[type]);

		const unsigned long long longlongmaxu64 = 
			pdatalayout->getTypeSizeInBits(getInt64Ty((*llvmctx))) < 64 ?
			~(LLONG_MIN >> sizeof(long long) * 8 - pdatalayout->getTypeSizeInBits(getInt64Ty((*llvmctx))) - 1)
				:
		ULLONG_MAX;

		const unsigned long long longlongmaxu128 =
			pdatalayout->getTypeSizeInBits(getInt128Ty((*llvmctx))) < 64 ?
			~(LLONG_MIN >> sizeof(long long) * 8 - pdatalayout->getTypeSizeInBits(getInt128Ty((*llvmctx))) - 1)
			:
		ULLONG_MAX;

		const long long longlongmax64 =
			pdatalayout->getTypeSizeInBits(getInt64Ty((*llvmctx))) < 64 ?
			~(LLONG_MIN >> sizeof(long long) * 8 - pdatalayout->getTypeSizeInBits(getInt64Ty((*llvmctx))))
			:
			LLONG_MAX;

		const long long longlongmax128 =
			pdatalayout->getTypeSizeInBits(getInt128Ty((*llvmctx))) < 64 ?
			~(LLONG_MIN >> sizeof(long long) * 8 - pdatalayout->getTypeSizeInBits(getInt128Ty((*llvmctx))))
			:
			LLONG_MAX;

#define CHECK_VAL_RANGE(range, TYPE) isunsigned ? (unsigned long long)val <= ((TYPE)range) : (long long)val <= ((TYPE)range)

		auto& currbasictype = currtype.back().spec.basicdeclspec;

		if (islonglong && isunsigned)
			goto ulonlong;
		else if (islonglong)
			goto longlong;
		else if (islong && isunsigned)
			goto ulong;
		else if (islong)
			goto slong;
		else if (isunsigned)
			goto uint;

		if (CHECK_VAL_RANGE(~(LLONG_MIN >> sizeof(long long) * 8 - pdatalayout->getTypeSizeInBits(getInt32Ty((*llvmctx)))), long long))
			currbasictype.basic[1] = "int";
		else
			uint:
		if (CHECK_VAL_RANGE(~(LLONG_MIN >> sizeof(long long) * 8 - pdatalayout->getTypeSizeInBits(getInt32Ty((*llvmctx))) - 1), unsigned long long)
			&& (base[type] != 10 || isunsigned))
			currbasictype.basic[1] = "int",
			currbasictype.basic[0] = "unsigned";
		else
			slong :
			if (CHECK_VAL_RANGE(longlongmax64, long long))
				currbasictype.basic[1] = "long",
				currbasictype.longspecsn = 1;
			else
				ulong :
				if (CHECK_VAL_RANGE(longlongmaxu64, unsigned long long))
					currbasictype.basic[0] = "unsigned",
					currbasictype.basic[1] = "long",
					currbasictype.longspecsn = 1;
				else
					longlong :
					if (CHECK_VAL_RANGE(longlongmax128, long long))
						currbasictype.basic[1] = "long",
						currbasictype.longspecsn = 2;
					else
						ulonlong :
						//for now 128bit literals are not supported if they are actually 128bit
						if (CHECK_VAL_RANGE(longlongmaxu128, unsigned long long)
							&& (base[type] != 10 || isunsigned))
							currbasictype.basic[0] = "unsigned",
							currbasictype.basic[1] = "long",
							currbasictype.longspecsn = 2;

		auto valval = llvm::ConstantInt::get(buildllvmtypefull(currtype), val, !isunsigned);

		immidiates.push_back({ currtype, valval });
	}
};

thread_local std::list<val>& basehndl::immidiates = ::immidiates;

const llvm::fltSemantics& getfloatsembytype(val val) {
	if (val.type.front().spec.basicdeclspec.basic[1] == "float")
		return llvm::APFloatBase::IEEEsingle();
	else {
		switch (val.type.front().spec.basicdeclspec.longspecsn)
		case 1:
			return llvm::APFloatBase::PPCDoubleDouble();
	}
	return llvm::APFloatBase::IEEEdouble();
}

struct handlefpexpr : basehndl {

	virtual llvm::Constant* getValZero(val val) override {

		return llvm::ConstantFP::getZero(val.value->getType(), false);
	}

	virtual std::list<struct type> getdefaulttype() override {
		auto basic = basicint;
		basic.spec.basicdeclspec.basic[1] = "float";
		return { basic };
	}

	virtual basehndl* (*getrestorefn())(basehndl*) override {
		return [](basehndl* pnhdl) -> basehndl* {
			return new (pnhdl) handlefpexpr{};
		};
	}

	virtual void getnegative() override {
		//immidiates.back() = integralpromotions(immidiates.back());

		immidiates.back().value = llvmbuilder->CreateFNeg(immidiates.back().value);
	}

	virtual llvm::Value* getlogicalnot() override {
		auto& op = immidiates.back();

		llvm::Value* originstr;

		originstr = op.value = llvmbuilder->CreateFCmp(
			llvm::CmpInst::Predicate::FCMP_OEQ, op.value,
			llvm::ConstantFP::get((*llvmctx), llvm::APFloat{ getfloatsembytype(op) }));

		op.type.erase(op.type.begin(), --op.type.end());

		op.value = CreateCastInst(op.value, getInt32Ty((*llvmctx)), false);

		extern void printvaltype(::val val);

		printvaltype(op);

		op.type.back().spec.basicdeclspec.basic[1] = "int",
			op.type.back().spec.basicdeclspec.basic[0] = "";

		return originstr;
	}

	virtual void mlutiplylasttwovalues() override {
		std::array ops = getops();

		ops[0].value = llvmbuilder->CreateFMul(ops[0].value, ops[1].value);

		immidiates.push_back(ops[0]);
	}

	virtual void dividelasttwovalues() override {
		std::array ops = getops();

		ops[0].value = llvmbuilder->CreateFDiv(ops[0].value, ops[1].value);

		immidiates.push_back(ops[0]);
	}

	virtual void modulolasttwovalues() override {
		std::array ops = getops();

		ops[0].value = llvmbuilder->CreateFRem(ops[0].value, ops[1].value);

		immidiates.push_back(ops[0]);
	}

	virtual void addlasttwovalues(bool bminus, bool busual) override {

		std::array ops = std::array{ *(----immidiates.end()), immidiates.back() };

		immidiates.erase(----immidiates.end(), immidiates.end());

		busual && (ops = usualarithmeticconversions(ops), 0),
			ops[0].value = llvmbuilder->CreateFAdd(
				ops[0].value,
				!bminus ? ops[1].value : llvmbuilder->CreateFNeg(ops[1].value));

		immidiates.push_back(ops[0]);
	}

	virtual void relatetwovalues(llvm::CmpInst::Predicate pred, llvm::CmpInst::Predicate unsignedpred, llvm::CmpInst::Predicate fltpred) override {
		std::array ops = getops();

		ops[0].value =
			llvmbuilder->CreateFCmp(fltpred, ops[0].value, ops[1].value);

		ops[0].value =
			CreateCastInst(ops[0].value, getInt32Ty((*llvmctx)), false);

		ops[0].type.erase(ops[0].type.begin(), --ops[0].type.end());

		ops[0].type.back().spec.basicdeclspec.basic[1] = "int",
			ops[0].type.back().spec.basicdeclspec.basic[0] = "";

		immidiates.push_back(ops[0]);
	}

	virtual void logictwovalues(bool bisand) override {
		getlogicalnot(), basehndl::getlogicalnot();
		basehndl::logictwovalues(bisand);
	}
};

struct handlecnstexpr : handlefpexpr {
	/*No branching needed for cnst expr*/
	virtual void begin_binary() { }
	virtual void begin_branch() { }
	virtual void end_binary() { }

	virtual void getaddress() override {
		immidiates.back().type.push_front({ type::POINTER });
	}

	virtual void push_imm(std::optional<std::list<::var>::reverse_iterator> var) override {
		extern void printvaltype(::val val);

		assert(var.has_value());

		val immidiate;


		llvm::Value* pglobal;

		immidiate.identifier = var.value()->identifier;

		printvaltype(immidiate);

		immidiate.lvalue = immidiate.value = var.value()->requestValue();

		immidiate.type = var.value()->type;

		phndl->immidiates.push_back(immidiate);

		printvaltype(immidiate);
	}

	virtual void constructstring() override {
		std::list<::type> stirngtype{ 1, ::type::ARRAY };

		stirngtype.front().spec.array.nelems = currstring.size() + 1;

		stirngtype.push_back({ ::type::BASIC });

		stirngtype.back().spec.basicdeclspec.basic[1] = "char";

		::val imm = {stirngtype, {}, "[[stringliteral]]"};

		imm.requestType();

		imm.constant = llvm::ConstantDataArray::getRaw(currstring, stirngtype.front().spec.array.nelems, (++imm.type.begin())->cachedtype);

		imm.isconstant = true;

		immidiates.push_back(imm);
	}

	virtual ::val create_val_tmp_aggregate(sub_range_ty iteratorty, _Ranges::subrange<std::list<::val>::iterator> immsiter) override {
		::val tmp{ {{iteratorty.begin(), iteratorty.end()}, {}, "[[initalizer_val_aggr]]"} };

		std::vector<llvm::Constant*> constantimmidiates;
		for (auto iter : immsiter) {
			constantimmidiates.push_back(iter.constant);
		}
		if(iteratorty.front().uniontype == type::BASIC) {
			if(iteratorty.front().spec.basicdeclspec.basic[0] == "struct") {
				tmp.requestType();
				tmp.constant = llvm::ConstantStruct::get(dyn_cast<llvm::StructType>(tmp.type.front().cachedtype), constantimmidiates);
			}
			else throw std::logic_error{"unsupported"};
		}
		else {
			tmp.type.front().spec.array.nelems = std::max((uint64_t)std::distance(immsiter.begin(), immsiter.end()), iteratorty.front().spec.array.nelems);

			tmp.constant = llvm::ConstantArray::get(dyn_cast<llvm::ArrayType>(tmp.requestType()), constantimmidiates);
		}

		//immidiates.insert(immsiter.end(), tmp);
		immidiates.erase(immsiter.begin(), immsiter.end());
		tmp.isconstant = true;
		return tmp;
	}

	virtual void init_end() override {
		adjus_aggregate_n_elems_if_needed();
		auto &targtvar = currtypevectorbeingbuild.back().p->back();
		auto resconst = convertTo(::immidiates.back(), targtvar.type);
		addvar(targtvar, resconst.constant);
	}

	virtual val convertTo(val target, std::list<::type> to, bool bdecay = true) override {
		bool comparetwotypesshallow(std::list<::type> one, std::list<::type> two);
		target = decay(target, target.isconstant);
		if (comparetwotypesshallow(target.type, to)) {
			target.type = to;
			return target;
		}

		printtype(buildllvmtypefull(to), "to");

		if (bIsBasicInteger(to.front()) && bIsBasicInteger(target.type.front()))
			target.constant = llvm::ConstantExpr::getIntegerCast(
				dyn_cast<llvm::ConstantInt>(target.constant), buildllvmtypefull(to),
				to.front().spec.basicdeclspec.basic[0] != "unsigned");
		else if(target.type.front().uniontype == type::POINTER || to.front().uniontype == type::POINTER ) {
			if(bIsBasicInteger(target.type.front()))
				target.value = llvm::ConstantExpr::getIntToPtr(target.constant, buildllvmtypefull(to));
			else if (bIsBasicInteger(to.front()))
				target.value = llvm::ConstantExpr::getPtrToInt(target.constant, buildllvmtypefull(to));
			else if (target.type.front().uniontype == type::ARRAY) {
				if ((++target.type.begin())->uniontype == type::BASIC
					&& (++target.type.begin())->spec.basicdeclspec.basic[1] == "char") {
					target.value = llvmbuilder->CreateGlobalStringPtr(
						dyn_cast<llvm::ConstantDataArray>(target.constant)
						->getAsCString(), "", 0);
				}
			}
		}
		else if(bIsBasicFloat(target.type.front()) || bIsBasicFloat(to.front())) {
			target.value = llvm::ConstantExpr::getFPCast(target.constant, buildllvmtypefull(to));
		}
		else if (target.type.front().uniontype == type::ARRAY && to.front().uniontype == type::ARRAY) {
			// In case we have array to char conversion
			// We might have excess elements to trim
	
			if ((++target.type.begin())->uniontype == type::BASIC && (++target.type.begin())->spec.basicdeclspec.basic[1] == "char"
				&&
				(++to.begin())->uniontype == type::BASIC && (++to.begin())->spec.basicdeclspec.basic[1] == "char"
				) {
					target.constant = llvm::ConstantDataArray::getString(*llvmctx,
						dyn_cast<llvm::ConstantDataArray>(target.constant)
						->getAsString().substr(0, to.front().spec.array.nelems), false);
				}
		}

		target.type = to;

		return target;
	}

	virtual basehndl* (*getrestorefn())(basehndl*) {
		return [](basehndl* pnhdl) -> basehndl* {
			return new (pnhdl) handlecnstexpr{};
		};
	}

	virtual void getnegative() override {
		immidiates.back().constant = llvm::ConstantExpr::getNeg(immidiates.back().constant);
	}

	using val = ::val;

	//std::list<val>& immidiates = basehndl::immidiates;

	/*auto getops(bool busual = true) {
		auto ops = basehndl::getops();

		return reinterpret_cast<std::array<val, 2>&&> (ops);
	}*/

	virtual void mlutiplylasttwovalues() override {
		std::array ops = getops();

		ops[0].constant = llvm::ConstantExpr::getMul(ops[0].constant, ops[1].constant);

		immidiates.push_back(ops[0]);
	}

	virtual void dividelasttwovalues() override {
		std::array ops = getops();

		if (ops[0].type.back().spec.basicdeclspec.basic[0] != "unsigned")
			ops[0].constant =
			llvm::ConstantExpr::get(llvm::Instruction::SDiv, ops[0].constant, ops[1].constant);
		else
			ops[0].constant =
			llvm::ConstantExpr::get(llvm::Instruction::UDiv, ops[0].constant, ops[1].constant);

		immidiates.push_back(ops[0]);
	}

	virtual void modulolasttwovalues() override {
		std::array ops = getops();

		if (ops[0].type.back().spec.basicdeclspec.basic[0] != "unsigned")
			ops[0].constant =
			llvm::ConstantExpr::get(llvm::Instruction::SRem, ops[0].constant, ops[1].constant);
		else
			ops[0].constant =
			llvm::ConstantExpr::get(llvm::Instruction::URem, ops[0].constant, ops[1].constant);

		immidiates.push_back(ops[0]);
	}

	virtual void addlasttwovalues(bool bminus, bool busual) override {
		assert(busual);
		std::array ops = getops();

		ops[0].constant = llvm::ConstantExpr::getAdd(
			ops[0].constant,
			!bminus ? ops[1].constant : llvm::ConstantExpr::getNeg(ops[1].constant));

		immidiates.push_back(ops[0]);
	}

	virtual void shifttwovalues(bool bright) override {
		std::array ops = getops(false);

		ops[0] = requireint(ops[0]);

		ops[0] = integralpromotions(ops[0]);

		ops[1] = integralpromotions(ops[1]);

		if (ops[1].type.front().uniontype == type::BASIC &&
			ops[0].constant->getType() != ops[1].constant->getType())
			ops[1].type = ops[0].type,
			ops[1].constant = CreateCastInst(
				ops[1].constant, ops[0].constant->getType(),
				ops[0].type.back().spec.basicdeclspec.basic[0] != "unsigned");

		if (!bright)
			ops[0].constant =
			llvm::ConstantExpr::getShl(ops[0].constant, ops[1].constant);
		else if (ops[0].type.back().spec.basicdeclspec.basic[0] != "unsigned")
			ops[0].constant =
			llvm::ConstantExpr::getAShr(ops[0].constant, ops[1].constant);
		else
			ops[0].constant =
			llvm::ConstantExpr::getLShr(ops[0].constant, ops[1].constant);

		immidiates.push_back(ops[0]);
	}

	virtual void relatetwovalues(llvm::CmpInst::Predicate pred, llvm::CmpInst::Predicate unsignedpred, llvm::CmpInst::Predicate fltpred) override {
		std::array ops = getops();

		if (ops[0].type.back().spec.basicdeclspec.basic[0] != "unsigned")
			ops[0].constant =
			llvm::ConstantExpr::getICmp(pred, ops[0].constant, ops[1].constant);
		else
			ops[0].constant = llvm::ConstantExpr::getCompare(unsignedpred, ops[0].constant,
				ops[1].constant);

		ops[0].constant =
			CreateCastInst(ops[0].constant, getInt32Ty((*llvmctx)), false);

		ops[0].type.erase(ops[0].type.begin(), --ops[0].type.end());
		;

		ops[0].type.back().spec.basicdeclspec.basic[1] = "int",
			ops[0].type.back().spec.basicdeclspec.basic[0] = "";

		immidiates.push_back(ops[0]);
	}

	virtual void bitwisetwovalues(llvm::Instruction::BinaryOps op) override {
		std::array ops = getops();

		ops[0].constant = llvm::ConstantExpr::get(op, ops[0].constant, ops[1].constant);

		immidiates.push_back(ops[0]);
	}

	virtual void logictwovalues(bool bisand) override {
		std::array ops = getops(false);

		ops[0].constant = llvm::ConstantExpr::getICmp(
			llvm::CmpInst::Predicate::ICMP_NE, ops[0].constant, getValZero(ops[0]));

		ops[1].constant = llvm::ConstantExpr::getICmp(
			llvm::CmpInst::Predicate::ICMP_NE, ops[1].constant, getValZero(ops[1]));

		ops[0].constant =
			!bisand ? llvm::ConstantExpr::getOr(ops[0].constant, ops[1].constant)
			: llvm::ConstantExpr::getAnd(ops[0].constant, ops[1].constant);

		ops[0].constant =
			CreateCastInst(ops[0].constant,
				getInt32Ty((*llvmctx)), false);

		ops[0].type.erase(ops[0].type.begin(), --ops[0].type.end());
		;

		ops[0].type.back().spec.basicdeclspec.basic[1] = "int",
			ops[0].type.back().spec.basicdeclspec.basic[0] = "";

		immidiates.push_back(ops[0]);
	}

	virtual llvm::Constant* CreateCastInst(llvm::Value* C, llvm::Type* Ty, bool bissigned) override {
		return llvm::ConstantExpr::getIntegerCast(llvm::dyn_cast<llvm::Constant> (C), Ty, bissigned);
	}
};

THREAD_LOCAL handlecnstexpr hndlcnstexpr{};

THREAD_LOCAL handlefpexpr hndlfpexpr{};

THREAD_LOCAL std::aligned_storage_t<sizeof(handlecnstexpr), alignof(handlecnstexpr)> unincompilingobj;

THREAD_LOCAL basehndl* phndl = new (&unincompilingobj) basehndl{};

//static std::remove_reference<decltype (basehndl::immidiates)>::type::iterator
//cnstexpriterstart{};

THREAD_LOCAL size_t szcnstexprinitial;

// static std::string currdeclidentifier{};

THREAD_LOCAL extern std::string currstring;

void printvaltype(val val) {
	if (!val.value)
		return;
	std::string type_str;
	llvm::raw_string_ostream rso(type_str);
	val.requestType()->print(rso);
	std::string name = val.value->getName().str();
	name = name.size() ? name : val.identifier;
	std::cout << name << " is " << rso.str() << std::endl;
}

DLL_EXPORT void obtainvalbyidentifier(std::unordered_map<unsigned, std::string>& hashmap) {
	obtainvalbyidentifier(hashmap["ident"_h]);
}

static val* plastnotfound;

/*extern "C" int
parse_filescope_var(const char *what, size_t sizewhat, int flags, unsigned long currpos, unsigned long continuefrom);*/

extern "C" unsigned int evalperlexpruv(const char *what);

static unsigned currtop;

static std::mutex maskchn;

static std::condition_variable maskchncondvar;

static std::mutex maskupd;

static std::condition_variable maskupdconvar;

static std::unordered_map<unsigned int, std::unordered_map<unsigned int, var>> scopevars_global;

THREAD_LOCAL static bool itervar_tmps_has_started;

THREAD_LOCAL static bool iterscope_has_started;

THREAD_LOCAL static bool itervar_tmps_has_extenral_could_not_be_checked;

THREAD_LOCAL static bool start_from_params_started;

THREAD_LOCAL static std::list<std::list<::var>>::reverse_iterator iterscope;

THREAD_LOCAL static std::list<::var>::reverse_iterator itervar;

THREAD_LOCAL static std::list<::var> tmps;

THREAD_LOCAL static std::list<::var>::reverse_iterator itervar_tmps;

THREAD_LOCAL static std::list<::var>::reverse_iterator start_from_params;

static void reset_obtainvalbyidentifier_search() {
	itervar_tmps_has_started = iterscope_has_started = itervar_tmps_has_extenral_could_not_be_checked = start_from_params_started = false;
}

static bool pop_obtainvalbyidentifier_last() {


	for (; iterscope != scopevar.rend(); ) {
		for (; itervar != iterscope->rend(); ) {
			iterscope->erase(itervar.base());
			return true;
		}
	}

	for (; itervar_tmps != tmps.rend(); ) {
		tmps.erase(itervar_tmps.base());
		return true;
	}

	return false;
}

const std::optional<std::list<::var>::reverse_iterator> obtainvalbyidentifier(std::string ident, bool push, bool bfindtypedef, bool bcontinue) {

	//unsigned long currpos = 0;
	//const unsigned long long lastpos = getcurrpos();

	std::optional<std::list<::var>::reverse_iterator> var{};

	//unsigned sofar = evalperlexpruv("scalar($nfilescopesrequested)");

	int id;

tryagain:
	if (push && scopevar.size() > 1) {
		auto& currfunctype = currfunc->type.front().spec.func.parametertypes_list.front();

		if(!start_from_params_started || !bcontinue) {
			start_from_params_started = bcontinue;
			start_from_params = currfunctype.rbegin();
		}

		if (start_from_params = std::find_if(
			start_from_params, currfunctype.rend(),
			[&](const ::var& param) { return param.identifier == ident; });
			start_from_params != currfunctype.rend())
		{
			var = start_from_params;
			++start_from_params;
			goto found;
		}
	}

	if(!iterscope_has_started || !bcontinue) {
checktmpagain:
		iterscope_has_started = bcontinue;
		iterscope = scopevar.rbegin();
		itervar = iterscope->rbegin();
	}

	for (; iterscope != scopevar.rend(); ++iterscope, itervar = iterscope->rbegin()) {
		for (; itervar != iterscope->rend(); ++itervar) {
			if (itervar->identifier == ident && (bfindtypedef == (itervar->linkage == "typedef"))) {
				var = itervar;
				++itervar;
				goto found;
			}
		}
	}

	if (!bcontinue || !itervar_tmps_has_extenral_could_not_be_checked) {

		itervar_tmps_has_extenral_could_not_be_checked = bcontinue;

		id = callstring("waitforid", ident.c_str(), ident.length());
		
		if (id != -1) {
			do {
				bool updated = false;
				//printf("looking for %d - %d\n", id, evalperlexpruv("pos()"));
				//registerndwait(id);
				//std::unique_lock lck{all};
				{
					std::unique_lock lck{boradcastingscope};

					assert(scopevars_global[stringhash(ident.c_str())].contains(id));

					scopevar.front().push_front(scopevars_global[stringhash(ident.c_str())][id]);
					scopevar.front().front().seralise(false);
					var = --scopevar.front().rend();
					for (auto i :_Ranges::reverse_view(_Ranges::iota_view<size_t, size_t>(0zu, id))) {
						scopevar.front().push_front(scopevars_global[stringhash(ident.c_str())][i]);
						scopevar.front().front().seralise(false);
						//updated = true;
						//var = tmps.rbegin();
						//goto found;
					}

					goto found;
				}

				//if (updated) {
					//goto checktmpagain;
				//}

				throw std::logic_error {"unreachable " + ident};
			}
			while (1);
		}
	}
	{
	undef: 
	if (push) {

		//if ((currpos = parse_file_scope_ident(ident, lastpos, currpos))) goto tryagain;

		std::cout << "not found: " << ident << std::endl;

		type fntype{ type::FUNCTION };

		fntype.spec.func.bisvariadic = true;

		::var newvar{ {.identifier = ident} };
		newvar.type = newvar.type = { fntype, basicint };
		newvar.firstintroduced = nullptr;
		newvar.ispotentiallywrong = true;
		scopevar.begin()->push_back(newvar);

		var = scopevar.begin()->rbegin();
		addvar(**var);

		/*if (push) {
			phndl->immidiates.push_back(::val{newvar});
			//plastnotfound = &phndl->immidiates.back();
		}
		return scopevar.begin()->rbegin();*/
		}
	}
	/*if (var->type.front ().uniontype == ::type::FUNCTION)
		phndl->immidiates.push_back (
			{pglobal = nonconstructable.mainmodule.getFunction (ident),
			 var->type, true});
	else if (pglobal = nonconstructable.mainmodule.getGlobalVariable (ident))
		phndl->immidiates.push_back ({pglobal, var->type, true});*/
found:
	if (!push) return var;

	phndl->push_imm(var);

	return var;
}

static THREAD_LOCAL std::list<std::list<::val>::iterator> curr_init_level_imms_pos_base;
static THREAD_LOCAL std::list<::val>::iterator curr_init_imm_pos;

using elem_init_type = std::list<sub_range_ty>;

struct elem_outter_type {
	elem_init_type first;
	elem_init_type::iterator second;
	std::list<::var>* third;
};

static THREAD_LOCAL std::list<elem_outter_type> last_init_trgt_type;

DLL_EXPORT void init_go_up_level(std::unordered_map<unsigned, std::string>& hashes) {
	auto &lastvar = currtypevectorbeingbuild.back().p->back();

	// See comment at the end of init_commit

	if (last_init_trgt_type.back().third &&
		((++last_init_trgt_type.back().third->begin())->type.begin()
			== last_init_trgt_type.back().second->begin() ||
			last_init_trgt_type.back().second != last_init_trgt_type.back().first.begin()
			)) {
		last_init_trgt_type.pop_back();
	}
	else {
		*last_init_trgt_type.back().second = {
			--last_init_trgt_type.back().second->begin(),
			last_init_trgt_type.back().second->end()};
	}
	auto last_imm_pos = curr_init_level_imms_pos_base.back(),
		next_imms_pos = last_imm_pos;
	auto val = phndl->create_val_tmp_aggregate({
		last_init_trgt_type.back().second->begin(),
		last_init_trgt_type.back().second->end()
		}
		, {++next_imms_pos, curr_init_imm_pos});
	curr_init_level_imms_pos_base.pop_back();
	auto to_insert = last_imm_pos; ++to_insert;

	curr_init_imm_pos = ::immidiates.insert(to_insert, val); ++curr_init_imm_pos;

	if (!last_imm_pos->value) {
		::immidiates.erase(last_imm_pos);
	}
}

extern std::list<::var>* getstructorunion(bascitypespec& basic);

DLL_EXPORT void init_go_down_level(std::unordered_map<unsigned, std::string>& hashes) {
	auto& lastvar = currtypevectorbeingbuild.back().p->back();

	if (last_init_trgt_type.back().second->front().uniontype == type::ARRAY) {
		*last_init_trgt_type.back().second = {
			++last_init_trgt_type.back().second->begin(),
			last_init_trgt_type.back().second->end()};
	}
	else if(last_init_trgt_type.back().second->front().uniontype == type::BASIC) {
		if (last_init_trgt_type.back().second->front().spec.basicdeclspec.basic[0] != "struct")
			throw std::logic_error{ "unsupported" };
		auto struc = getstructorunion(last_init_trgt_type.back().second->front().spec.basicdeclspec);
		
		elem_init_type types_members;

		std::transform(++struc->begin(), struc->end(), std::back_inserter(types_members),
			[](::var& elem) {
				return sub_range_ty{elem.type.begin(), elem.type.end()};
			}
		);

		last_init_trgt_type.push_back({ types_members, {}, struc });

		last_init_trgt_type.back().second = last_init_trgt_type.back().first.begin();
	}
	else {
		throw std::logic_error{ "invalid aggregate initalisation indirection" };
	}

	if (::immidiates.size() < 2, true) {
		::immidiates.resize(::immidiates.size() + 1);
		curr_init_level_imms_pos_base.push_back({ ----::immidiates.end() });
		curr_init_imm_pos = --::immidiates.end();
	}
	else {
		curr_init_level_imms_pos_base.push_back({ ----::immidiates.end() });
	}
	
}

DLL_EXPORT void init_end(std::unordered_map<unsigned, std::string>& hashes) {
	if (!::immidiates.back().value)
		::immidiates.pop_back();
	last_init_trgt_type.pop_back();
	curr_init_level_imms_pos_base.pop_back();
	phndl->init_end();
	::immidiates.resize(1);
	if (scopevar.size() == 1) {
		endconstantexpr();
	}
}

DLL_EXPORT void init_commit() {

	auto& lastvar = currtypevectorbeingbuild.back().p->back();


	auto curr_imm = ::immidiates.back();

	::immidiates.pop_back();

	auto type = std::list<::type>{ last_init_trgt_type.back().second->begin(), last_init_trgt_type.back().second->end()};

	*curr_init_imm_pos = phndl->convertTo(curr_imm, type);

	++curr_init_imm_pos;

	if (curr_init_imm_pos == ::immidiates.end()) {
		::immidiates.resize(::immidiates.size() + 1);
		curr_init_imm_pos = --::immidiates.end();
	}

	// If it's a struct we are aggregate initialising 
	// iterate to next member

	// It would be a struct if we have not confined
	// the current type range

	// So this would mean that currnt type range will begin
	// at the same point as current type list pointer

	// Also once we advance the check is if we are in different 
	// than the first element in the types list

	if (last_init_trgt_type.back().third &&
		((++last_init_trgt_type.back().third->begin())->type.begin()
		== last_init_trgt_type.back().second->begin() ||
			last_init_trgt_type.back().second != last_init_trgt_type.back().first.begin()
			)
		) {
		++last_init_trgt_type.back().second;
	}
}

extern std::list<::var>* getstructorunion(bascitypespec& basic);

uint64_t getConstantIntegerValue(const ::val &value);

DLL_EXPORT void go_to_level(std::unordered_map<unsigned, std::string>& hashes) {
	std::string ident_to_adjust_to = hashes["dsig_ident"_h];

	if(!ident_to_adjust_to.empty()) {
		auto pstruct = last_init_trgt_type.back().third;
		last_init_trgt_type.back().second = last_init_trgt_type.back().first.begin();
		for (auto &mem : *pstruct | _Ranges::views::drop(1)) {
			if(mem.identifier == ident_to_adjust_to) break;
			++last_init_trgt_type.back().second;
			++curr_init_imm_pos;

			if (curr_init_imm_pos == ::immidiates.end()) {
				::immidiates.resize(::immidiates.size() + 1);
				curr_init_imm_pos = --::immidiates.end();
			}
		}
	}
	else {
		size_t number = getConstantIntegerValue(::immidiates.back());
		::immidiates.pop_back();

		if (number >= ::immidiates.size()) {
			::immidiates.resize(number + 1);
		}

		curr_init_imm_pos = curr_init_level_imms_pos_base.back();

		std::advance(curr_init_imm_pos, number);
	}
}

DLL_EXPORT void begin_initializer(std::unordered_map<unsigned, std::string>& hashes) {
	auto &lastvar = currtypevectorbeingbuild.back().p->back();

	lastvar.requestType();

	elem_init_type elem_ty{ sub_range_ty{lastvar.type.begin(), lastvar.type.end()}};

	last_init_trgt_type = { {elem_ty, {}, nullptr} };

	last_init_trgt_type.back().second = last_init_trgt_type.back().first.begin();

	curr_init_level_imms_pos_base = { curr_init_imm_pos = --::immidiates.end() };

	if (scopevar.size() == 1)
		beginconstantexpr();
}

DLL_EXPORT void addplaintexttostring(std::unordered_map<unsigned, std::string>& hashes) {
	currstring += std::string{ hashes["textraw"_h] };
}

DLL_EXPORT void addescapesequencetostring(std::unordered_map<unsigned, std::string>& hashes) {
	std::string escape{ hashes["escaperaw"_h] };

	switch (stringhash(escape.c_str())) {
	case "\\n"_h:
		currstring += '\n';
		return;
	case "\\'"_h:
		currstring += '\'';
		return;
	case "\\\""_h:
		currstring += '\"';
		return;
	case "\\\\"_h:
		currstring += '\\';
		return;
	case "\\a"_h:
		currstring += '\a';
		return;
	case "\\b"_h:
		currstring += '\b';
		return;
	case "\\f"_h:
		currstring += '\f';
		return;
	case "\\r"_h:
		currstring += '\r';
		return;
	case "\\t"_h:
		currstring += '\t';
		return;
	case "\\v"_h:
		currstring += '\v';
		return;
	case "\\0"_h:
		currstring += '\0';
		return;
	}

	escape.erase(0, 2);

	currstring += (char)std::stoi(escape, nullptr, hashes.contains("ishex"_h) ? 0x10 : 8);
}

DLL_EXPORT void begin_ternary() {
	var tmp{ {{basicint}} };

	addvar(tmp);

	tmp.identifier = "[[ternary]]";

	startifstatement(true);

	immidiates.push_back(val{ tmp, tmp.value });
}

DLL_EXPORT void continueifstatement();

DLL_EXPORT void mid_ternary() {
	auto tmptern = *----immidiates.end();

	phndl->assigntwovalues();

	continueifstatement();

	immidiates.pop_back();
	immidiates.push_back(tmptern);
}

DLL_EXPORT void endifstatement();

DLL_EXPORT void end_ternary() {
	auto tmptern = *----immidiates.end();

	phndl->assigntwovalues();

	endifstatement();

	tmptern.value = llvmbuilder->CreateLoad(tmptern.requestType(), tmptern.lvalue);

	immidiates.pop_back();
	immidiates.push_back(tmptern);
}

DLL_EXPORT void comma() {
	immidiates.pop_back();
}

static std::string mangle(std::list<::type> type);

static std::string manglefnparameters(::type type) {
	std::stringstream fntype;
	std::list<std::list<::type>> fnparamtypes;

	std::transform(
		type.spec.func.parametertypes_list.front().begin(), type.spec.func.parametertypes_list.front().end(), std::back_inserter(fnparamtypes),
		[&](::var elem) { return elem.type; });
	fntype << "(";
	for (auto curr : fnparamtypes)
		fntype << mangle(curr) << ",";
	fntype << "[[nothing]])";
	return fntype.str();
}

static std::string mangle(std::list<::type> type) {
	std::stringstream ss;

	ss << "_type_";

	for (auto curr : type) {
		(curr.uniontype == type::ARRAY && (ss << "[" << curr.spec.array.nelems << "]", true))
			|| (curr.uniontype == type::BASIC && (ss << (std::string)curr.spec.basicdeclspec, true))
			|| (curr.uniontype == type::FUNCTION && (ss << manglefnparameters(curr), true))
			|| (curr.uniontype == type::POINTER && (ss << "*", true));
	}

	return ss.str();
}

static bool comparefunctiontypeparameters(::type fntypeone, ::type fntypetwo);

static ::var *reqeustInitialFn(std::string ident) {

	std::optional<std::list<::var>::reverse_iterator> iter;

	static THREAD_LOCAL std::unordered_map<std::string, ::var*> fastmap;

	if(fastmap.contains(ident)) return fastmap[ident];

	while(auto val = obtainvalbyidentifier(ident, false, false, true)) {
		//if (iter->value)

		iter = val.value();
	}

	reset_obtainvalbyidentifier_search();

	iter.value()->requestType();

	return fastmap[ident] = &*iter.value();
}

bool comparetwotypesdeep(std::list<::type> first, std::list<::type> second);

static bool comparefunctiontypeparameters(::type fntypeone, ::type fntypetwo) {
	auto& paramslistone = fntypeone.spec.func.parametertypes_list.front(),
		& paramslisttwo = fntypetwo.spec.func.parametertypes_list.front();

	auto iterparamsone = paramslistone.begin(), iterparamstwo = paramslisttwo.begin();

	while (iterparamsone != paramslistone.end() && iterparamstwo != paramslisttwo.end()
		&& comparetwotypesdeep(iterparamsone->type, iterparamstwo->type))
		++iterparamsone, ++iterparamstwo;

	return iterparamsone == paramslistone.end() && iterparamstwo == paramslisttwo.end();
}

//static std::unordered_map<unsigned, bool> overloadflag;

void addvar(var& lastvar, llvm::Constant* pInitializer) {

	const char* lastvartypestoragespec = lastvar.linkage.c_str();

	assert(lastvar.linkage != "typedef");
	//	for (lastvar.pValue = nullptr /*(llvm::Value *)lastvar.pllvmtype*/;;)
	//		return;

	if (lastvar.type.front().uniontype == type::FUNCTION || !lastvar.linkage.empty())
		goto extrnl_decl;

	if (!lastvar.firstintroduced) {
	extrnl_decl:
		//case 1:
		llvm::GlobalValue::LinkageTypes linkagetype;

		switch (stringhash(lastvartypestoragespec)) {
		default:
		case "extern"_h:
			linkagetype = llvm::GlobalValue::LinkageTypes::ExternalLinkage;
			break;
		case "static"_h:
			linkagetype = llvm::GlobalValue::LinkageTypes::InternalLinkage;
		}

		switch (lastvar.type.front().uniontype) {
		case type::POINTER:
		case type::ARRAY:
		case type::BASIC:
		{
			auto typevar = lastvar.requestType();

			//pInitializer ? pInitializer->mutateType(typevar) : (void)0;

			lastvar.value = mainmodule->getGlobalVariable(lastvar.identifier);
			
			lastvar.value || (lastvar.value = new llvm::GlobalVariable(
				*mainmodule, typevar, false,
				linkagetype,
				nullptr,
				lastvar.identifier));

			std::string type_str;
			llvm::raw_string_ostream rso(type_str);
			lastvar.pllvmtype->print(rso);

			auto dibasicty = llvmdibuilder->createArrayType(0, 0, llvmdibuilder->createBasicType(rso.str(), pdatalayout->getTypeStoreSizeInBits(lastvar.pllvmtype), llvm::dwarf::getAttributeEncoding("DW_ATE_unsigned_char")), {});

			if(lastvar.linkage.empty()) {
				
				llvmdibuilder->createGlobalVariableExpression(llvmcu->getFile(), lastvar.identifier, lastvartypestoragespec, llvmcu->getFile(), evalperlexpruv("pos()"), 
				dibasicty, false);
				dyn_cast<llvm::GlobalVariable>(lastvar.value)->setInitializer(pInitializer ? pInitializer : llvm::Constant::getNullValue(typevar));
			}
			else {
				llvmdibuilder->createTempGlobalVariableFwdDecl(llvmcu->getFile(), lastvar.identifier, lastvartypestoragespec, llvmcu->getFile(), evalperlexpruv("pos()"),
				dibasicty, false);
			}
			// scopevar.front ().push_back (lastvar);
			break;
		}
		case type::FUNCTION:
			printtype(lastvar.requestType(), lastvar.identifier);
			auto initialfn = reqeustInitialFn(lastvar.identifier);
			bool ismangle = initialfn && !comparefunctiontypeparameters(lastvar.type.front(), initialfn->type.front()) ;
 			std::string mangledfnname = lastvar.identifier;
			if (ismangle) {
				mangledfnname += mangle(lastvar.type);
			}
			if(!allowccompat && mangledfnname.size() > 1 && mangledfnname.starts_with("_")) {
				mangledfnname.erase(mangledfnname.begin());
			}

			if (auto funcval = mainmodule->getFunction(mangledfnname)) {
				lastvar.value = funcval;
			}
			else {
				lastvar.value = llvm::Function::Create(
					llvm::dyn_cast<llvm::FunctionType> (lastvar.requestType()),
					linkagetype, mangledfnname, *mainmodule
				);
				if (!lastvar.type.front().spec.func.callconv.empty()) {
					dyn_cast<llvm::Function>(lastvar.value)->setCallingConv(llvm::CallingConv::X86_StdCall);
				}
			}
			assert(lastvar.value);
			// scopevar.front ().push_back (lastvar);

			break;
		}
	}	//break;
	else {
		//default:
		printtype(lastvar.requestType(), lastvar.identifier);
		llvmbuilder->SetInsertPoint(&dyn_cast<llvm::Function>(currfunc->value)->front(),
			dyn_cast<llvm::Function>(currfunc->value)->front().begin());
		lastvar.value = llvmbuilder->CreateAlloca(lastvar.requestType(), nullptr,
			lastvar.identifier);
		std::string type_str;
		llvm::raw_string_ostream rso(type_str);
		lastvar.pllvmtype->print(rso);

		auto dibasicty = llvmdibuilder->createArrayType(0, 0, llvmdibuilder->createBasicType(rso.str(), pdatalayout->getTypeStoreSizeInBits(lastvar.pllvmtype), llvm::dwarf::getAttributeEncoding("DW_ATE_unsigned_char")),{});
		auto localvar = llvmdibuilder->createAutoVariable(llvmsub, lastvar.identifier, llvmcu->getFile(), evalperlexpruv("pos()"), dibasicty);
		llvmdibuilder->insertDeclare(lastvar.value, localvar, llvmdibuilder->createExpression(), llvm::DILocation::get(*llvmctx, evalperlexpruv("pos()"), 0, llvmsub), llvmbuilder->GetInsertBlock());
		llvmbuilder->SetInsertPoint(pcurrblock.back());
	}
}

THREAD_LOCAL extern std::pair<std::string, std::string> currstruct;

DLL_EXPORT void endqualifs(std::unordered_map<unsigned, std::string>&& hashes);

THREAD_LOCAL static std::list<std::list<var>>::iterator laststruc;

DLL_EXPORT void check_stray_struc() {
	// Currently we only care about nested structures or unions
	if (currtypevectorbeingbuild.back().currdecltype != currdecltypeenum::STRUCTORUNION) {
		return;
	}
	auto& lastmembers = *laststruc;
	auto& structvar = lastmembers.front();

	if (structvar.identifier.empty()) {
		currtypevectorbeingbuild.back().p->push_back(structvar);
		auto extraptr = currtypevectorbeingbuild.back().p->back().type.front().spec.basicdeclspec.extra = std::make_shared<extra_basic_union>();
		extraptr->~extra_basic_union();
		new (extraptr->target_raw) annon_struc_mem{};
		reinterpret_cast<annon_struc_mem*>(extraptr->target_raw)->annonstruct = lastmembers;
	}
}

DLL_EXPORT void endbuildingstructorunion() {

	//for (auto& a : lastmembers | _Ranges::views::drop(1))
		//a.pllvmtype = buildllvmtypefull(a.type);

	/*std::vector<llvm::Type*> structtypes;

	std::transform(++lastmembers.begin(), lastmembers.end(),
		std::back_inserter(structtypes),
		[](const var& elem) { return elem.pllvmtype; });*/

	laststruc = currtypevectorbeingbuild.back().p;

	currtypevectorbeingbuild.pop_back();

	laststruc->front().linkage = "[[completed]]";

	if (pcurrblock.empty() && !laststruc->front().identifier.empty())  {
		auto fullident = laststruc->front().type.front().spec.basicdeclspec.basic[0] +  " " + laststruc->front().type.front().spec.basicdeclspec.basic[3];
		auto idtostore = callstring("getidtostor", fullident.c_str(), fullident.length());
		assert(idtostore != -1);
		auto elemtopush = *laststruc;
		for (auto &elem : elemtopush) {
			elem.seralise(false);
		}
		{
			std::unique_lock lck{boradcastingstrc};
			structorunionmembers_global[stringhash(fullident.c_str())][idtostore] = std::move(elemtopush);
		}
		callint("broadcastid", idtostore, fullident.c_str(), fullident.size());
	}

	//assert(structvar.type.back().spec.basicdeclspec.basic[0] == "struct");

	//dyn_cast<llvm::StructType> (structvar.pllvmtype)->setBody(structtypes);

	//currstruct.first = structvar.type.back().spec.basicdeclspec.basic[0];
	//currstruct.second = structvar.type.back().spec.basicdeclspec.basic[3];

	//static_cast<basic_type_origin&>(structvar.type.back().spec.basicdeclspec) = basic_type_origin{ iterunorstrtype{} };

	//structvar.type.back().spec.basicdeclspec.iterunorstr = structorunionmembers.back().end();
}

bool bIsBasicFloat(const type& type);

bool bIsBasicInteger(const type& type) {
	std::set integertraits{ "unsigned", "signed", "" };
	return type.uniontype == type::BASIC
		&& !type.spec.basicdeclspec.basic[1].empty()
		&& _Ranges::find(integertraits, type.spec.basicdeclspec.basic[0]) != integertraits.end() && !bIsBasicFloat(type);
}

bool bIsBasicFloat(const type& type) {
	return type.uniontype == type::BASIC
		&& _Ranges::contains(std::array{ "float", "double" }, type.spec.basicdeclspec.basic[1]);
}

bool comparetwotypesdeep(std::list<::type> first, std::list<::type> second) {
	auto itertypeone = first.begin(), itertypetwo = second.begin();

	while (itertypeone != first.end() && itertypetwo != second.end()
		&& itertypeone->uniontype == itertypetwo->uniontype && (
			(itertypetwo->uniontype == type::ARRAY && itertypeone->spec.array.nelems == itertypetwo->spec.array.nelems) 
			|| (itertypetwo->uniontype == type::BASIC && itertypeone->spec.basicdeclspec == itertypetwo->spec.basicdeclspec)
			|| (itertypetwo->uniontype == type::FUNCTION && comparefunctiontypeparameters(*itertypeone, *itertypetwo))
			|| (itertypetwo->uniontype == type::POINTER && true)))
		++itertypetwo, ++itertypeone;

	return itertypeone == first.end() && itertypetwo == second.end();
}

bool comparetwotypesshallow(std::list<::type> one, std::list<::type> two) {
	auto iterone = one.begin(), itertwo = two.begin();
	{

	switch (iterone->uniontype)
		if (0) case type::ARRAY:
			return itertwo->uniontype == iterone->uniontype && itertwo->spec.array.nelems == iterone->spec.array.nelems;
		else if (0)
		case type::POINTER:
		case type::FUNCTION:
			return itertwo->uniontype == iterone->uniontype;
		else if (0) case type::BASIC:
			return itertwo->uniontype == iterone->uniontype && itertwo->spec.basicdeclspec == iterone->spec.basicdeclspec;
	}
	return false;
}

val coerceto(val target, std::list<::type> to) {
	if (comparetwotypesshallow(target.type, to)) {
		target.type = to;
		return target;
	}

	if(target.type.front().uniontype == type::FUNCTION) {
		target.type.pop_front();
	}

	if (to.front().uniontype == type::BASIC && to.front().spec.basicdeclspec.basic[1] == "[[nbitint]]") {
		to.front().spec.basicdeclspec.longspecsn = pdatalayout->getTypeSizeInBits(target.requestType());
		to.front().cachedtype = nullptr;
	}

	var tmp = var{ to };
	addvar(tmp);

	llvm::Value* rvalue;
	
	if(target.lvalue)
		rvalue = llvmbuilder->CreateLoad(tmp.pllvmtype, target.lvalue);
	else {
		var tmprval = var{ {target.type, nullptr, "[[tmprval]]"} };
		addvar(tmprval);
		llvmbuilder->CreateStore(target.value, tmprval.value);
		rvalue = llvmbuilder->CreateLoad(tmp.pllvmtype, tmprval.value);
	}

	/*if(tmp.requestType()->isIntegerTy())
		llvmbuilder->CreateStore(phndl->getValZero(val{tmp}), tmp.value);*/

	val ret = { tmp };

	ret.value = rvalue;
	ret.lvalue = target.lvalue;

	return ret;
}

val convertTo(val target, std::list<::type> to, bool bdecay) {

	return phndl->convertTo(target, to, bdecay);
}

DLL_EXPORT void applycast() {
	auto& lasttypevar = currtypevectorbeingbuild.back().p->back();

	//currtypevectorbeingbuild.back().p->pop_back();

	auto& currtype = lasttypevar.type;

	//std::rotate(currtype.begin(), currtype.begin() + 1, currtype.end());

	auto target = phndl->immidiates.back();

	phndl->immidiates.pop_back();

	target = convertTo(target, currtype, currtype.front().uniontype == type::POINTER && target.lvalue);

	phndl->immidiates.push_back(target);

	currtypevectorbeingbuild.back().p->pop_back();
}

extern std::list<::var>* getstructorunion(bascitypespec& basic);

void pushsizeoftype(val&& value) {
	size_t szoftype = 1;

	szoftype = pdatalayout->getTypeStoreSizeInBits(value.requestType()) / 8;

	phndl->immidiates.push_back(
		val{ std::list{basicsz()},
		llvm::ConstantInt::getIntegerValue(
				pdatalayout->getPointerSizeInBits() == 64 ? getInt64Ty((*llvmctx)) : getInt32Ty((*llvmctx)),
				llvm::APInt{pdatalayout->getPointerSizeInBits(), szoftype}),
			"[[sizeoftypename]]" });
}

bool memberaccess_decoy(std::string ident) {

	auto& lastvar = phndl->immidiates.back();

	auto pliststruct = //lastvar.type.front().spec.basicdeclspec.iterunorstr;
		getstructorunion(lastvar.type.front().spec.basicdeclspec);

	auto imember = 0;

	auto listiter = ++pliststruct->begin();

	auto lastvarcopy = lastvar;

	for (; listiter != pliststruct->end() &&
		listiter->identifier != ident;
		++imember, ++listiter)
		if (listiter->identifier.empty()) {
			if (lastvarcopy.type.front().spec.basicdeclspec.basic[0] != "union") {
				goto exec_member;
			}
			else {
				lastvar = coerceto(lastvar, listiter->type);
			}
		continue_search:
			if (memberaccess_decoy(ident))
				return true;
		}

	if (listiter == pliststruct->end())
		return false;

	if (lastvarcopy.type.front().spec.basicdeclspec.basic[0] == "union") {
		lastvar = coerceto(lastvarcopy, listiter->type);
		return true;
	}

exec_member:
	{
		auto& lastvar = phndl->immidiates.back();

		lastvar = lastvarcopy;

		auto& lastlvalue = lastvar.lvalue;


		auto& member = *listiter;

		llvm::Value* lvalue = llvmbuilder->CreateGEP(
			pliststruct->front().pllvmtype,
			lastvar.lvalue,

			{ llvmbuilder->getInt32(0), llvmbuilder->getInt32(imember) });

		//printtype(member.pllvmtype->getPointerTo(), "");

		// lvalue = llvmbuilder->CreatePointerCast(lvalue,
		// member.pllvmtype->getPointerTo());

		printtype(member.pllvmtype,
			lastvar.identifier + " " + std::to_string(imember));

		llvm::Value* rvalue = llvmbuilder->CreateLoad(member.pllvmtype, lvalue);

		lastvar.type = member.type;

		lastvar.identifier = member.identifier;

		lastvar.value = rvalue;

		printvaltype(lastvar);

		lastvar.lvalue = lvalue;

		if (member.identifier.empty()) {
			goto continue_search;
		}
	}

	return true;
}

DLL_EXPORT void memberaccess(std::unordered_map<unsigned, std::string>& hashentry) {
	bool indirection = hashentry["arrowordotraw"_h] == "->";

	if (indirection) phndl->applyindirection();

	assert(memberaccess_decoy(hashentry["ident_member"_h]));
}

DLL_EXPORT void endsizeoftypename() {

	auto currtype = currtypevectorbeingbuild.back().p->back();

	//std::rotate(currtype.begin(), currtype.begin() + 1, currtype.end());

	currtypevectorbeingbuild.back().p->pop_back();

	pushsizeoftype(val{ currtype });
}

THREAD_LOCAL std::list<std::pair<std::array<llvm::BranchInst*, 2>, llvm::BasicBlock*>> ifstatements{ 1 };

llvm::BranchInst* splitbb(const char* identifier, size_t szident);

DLL_EXPORT void insertinttoimm(const char* str, size_t szstr, const char* suffix, size_t szstr1, int type);

DLL_EXPORT void startifstatement() {
	startifstatement(true);
}

std::list<std::pair<std::array<llvm::BranchInst*, 2>, llvm::BasicBlock*>>::iterator startifstatement(bool pop) {
	auto dummyblock = llvm::BasicBlock::Create((*llvmctx), "", dyn_cast<llvm::Function> (currfunc->requestValue()));

	if (!immidiates.size())
		insertinttoimm("1", sizeof "1" - 1, "", 0, 3);

	auto firstnot = phndl->getlogicalnot();

	auto lastnot = phndl->basehndl::getlogicalnot();

	splitbb("", 0);

	auto value = llvmbuilder->CreateIntCast(immidiates.back().value, llvm::IntegerType::get((*llvmctx), 1), true);

	ifstatements.push_back({ {llvmbuilder->CreateCondBr(value, dummyblock, dummyblock)}, dummyblock });

	splitbb("", 0);

	ifstatements.back().first[0]->setSuccessor(0, pcurrblock.back());

	if (pop)
		immidiates.pop_back();

	return --ifstatements.end();
}

DLL_EXPORT void continueifstatement() {
	ifstatements.back().first[1] = splitbb("", 0);
	ifstatements.back().first[0]->setSuccessor(1, pcurrblock.back());
}

DLL_EXPORT void endifstatement() {
	splitbb("", 0);
	if (auto lastbranchif = ifstatements.back().first[1])
		lastbranchif->setSuccessor(0, pcurrblock.back());

	if (ifstatements.back().first[0]->getSuccessor(1) == ifstatements.back().second)
		ifstatements.back().first[0]->setSuccessor(1, pcurrblock.back());

	ifstatements.back().second->eraseFromParent();
	ifstatements.pop_back();
}

DLL_EXPORT void beginbinary() {

	opsscopeinfo.push_back({ --immidiates.end(), var{std::list{type{type::BASIC}}}, --ifstatements.end() });

	//std::pair<var, decltype (immidiates)::iterator> currlogicelem;

	opsscopeinfo.back().currlogicopvar.type.back().spec.basicdeclspec.basic[1] = "int";

	opsscopeinfo.back().currlogicopvar.pllvmtype = buildllvmtypefull(opsscopeinfo.back().currlogicopvar.type);

	addvar(opsscopeinfo.back().currlogicopvar);

	/*var result{{type::BASIC}};

	result.type.back ().spec.basicdeclspec.basic[1] = "int";

	result.pllvmtype = buildllvmtypefull (result.type);

	addvar (result);

	val imm = result;

	insertinttoimm ("1", sizeof "1", "", 0, 3);

	imm.value = llvmbuilder->CreateLoad (imm.value);
	immidiates.push_back (imm);

	phndl->assigntwovalues();

	currlogicopval.push_back (result);
	opbbs.push_back ({});
	beginlogicalop (1);*/
	//currlogicopval.back ().second = --immidiates.end ();
}

DLL_EXPORT void endbinary() {

	auto opscopinf = opsscopeinfo.back();

	opsscopeinfo.pop_back();

	auto lastimm = immidiates.back();

	immidiates.erase(++opscopinf.immidiatesbegin, immidiates.end());

	immidiates.push_back(lastimm);

	//if (immidiates.back ().identifier == "[[logicop]]")
	//immidiates.back ().value = llvmbuilder->CreateLoad (immidiates.back ().value);

	/*if (opbbs.back ().second.value)
		immidiates.pop_back (),
			immidiates.push_back (opbbs.back ().second);

	currlogicopval.pop_back ();
	opbbs.pop_back ();*/
	//if(phndl->opbbs.size())
	//phndl->endlast(phndl->opbbs.back().first, phndl->opbbs.back().second);

	//opbbs.pop_back ();

	//if(currlogicopval.pValue)
	//immidiates.push_back(currlogicopval);

	//currlogicopval.pValue = nullptr;
}

DLL_EXPORT void endsizeofexpr() {
	auto lastimmtype = phndl->immidiates.back();
	phndl->immidiates.pop_back();
	pushsizeoftype(std::move(lastimmtype));
}

/*DLL_EXPORT void adddeclarationident(const char* str, size_t szstr,
	bool bistypedef) {
	std::string ident{ str, szstr };

	currtypevectorbeingbuild.back().p->back().identifier = ident;

	//currtypevectorbeingbuild.back().p->back().bistypedef = currtypevectorbeingbuild.back().p->back().type.back().spec.basicdeclspec.basic[2] == "typedef";
}*/

//DLL_EXPORT void finalizedeclaration() { endpriordecl(); }

void fixupstructype(std::list<::var>* var) {
	std::vector<llvm::Type*> tmp;

	size_t currsz = 0;

	size_t curralign = 1;

	if (var->front().type.front().spec.basicdeclspec.basic[0] == "union") {
		var->sort(
			[&](const ::var &first, const ::var& second) -> bool {
				if (&first == &var->front())
					return true;
				else if (&second == &var->front())
					return false;
				return 
					pdatalayout->getTypeAllocSize(const_cast<::var&>(first).requestType()) >
					pdatalayout->getTypeAllocSize(const_cast<::var&>(second).requestType());
			}
		);
		var->front().pllvmtype = (++var->begin())->pllvmtype;

		return;
	}

	auto structtypes = mainmodule->getIdentifiedStructTypes();

	auto foundstruc = std::find_if(structtypes.begin(), structtypes.end(), [&](llvm::StructType *pstructype) {
		return pstructype->getStructName() == var->front().identifier;
	});

	if(foundstruc != structtypes.end()) {

		var->front().pllvmtype = *foundstruc;

	} else {

		var->front().pllvmtype = llvm::StructType::create((*llvmctx), var->front().identifier);

	}

	for (auto& a : *var | _Ranges::views::drop(1))
		if (!a.pllvmtype)
			a.fixupTypeIfNeededBase(),
			a.pllvmtype = (llvm::Type*)-1ULL,
			tmp.push_back(buildllvmtypefull(a.type));

	auto& structvar = var->front();

	auto iter_var = ++var->begin();

	std::for_each(tmp.begin(), tmp.end(),
		[&iter_var](const llvm::Type* elem) {
			iter_var++->pllvmtype = const_cast<llvm::Type*>(elem);
		});

	if(dyn_cast<llvm::StructType> (structvar.pllvmtype)->isOpaque())

		dyn_cast<llvm::StructType> (structvar.pllvmtype)->setBody(tmp);
}

std::list<::var>* getstructorunion(bascitypespec& basic) {
	std::list<::var>* var = nullptr;

	//unsigned long currpos = 0;
	//const unsigned long long lastpos = getcurrpos();

	std::string ident = basic.basic[3];

	bool triedagain = false;

	if(!ident.empty()) {
tryagain:
	std::find_if(structorunionmembers.rbegin(), structorunionmembers.rend(),
		[&](std::list<std::list<::var>>& scope) {
			auto iter = std::find_if(
				scope.rbegin(), scope.rend(),
				[&](const std::list<::var>& scopevar) {
					return scopevar.front().identifier == ident &&
						scopevar.front().type.front().spec.basicdeclspec.basic[0] == basic.basic[0]
						 && scopevar.front().linkage == "[[completed]]";
				});

			if (iter != scope.rend())
				return var = &*iter, true;
			return false;
		});

		if (!var) {

			//unsigned sofar = evalperlexpruv("scalar($nfilescopesrequested)");

			std::string fullident = basic.basic[0] + " " + ident;

			auto id = callstring("waitforid", fullident.c_str(), fullident.length());
			
			if (id != -1) {
				do {
					assert(!triedagain);
					//printf("looking for %d - %d\n", id, evalperlexpruv("pos()"));
					//registerndwait(id);

					if (structorunionmembers_global[stringhash(fullident.c_str())].contains(id)) {
						std::unique_lock lck{boradcastingstrc};
						structorunionmembers.front().push_front(structorunionmembers_global[stringhash(fullident.c_str())][id]);
						for (auto &var : structorunionmembers.front().front()) {
							var.seralise(false);
						}
						//triedagain = true;
						//goto tryagain;
						var = &structorunionmembers.front().front();
						assert(var->front().linkage == "[[completed]]");
						assert(!var->front().pllvmtype);
						break;
					}

					throw std::logic_error {"unreachable " + fullident};
				}
				while (1);
			}
		}
	}
test:
	if (!var) 
	if (auto pstr = dynamic_cast<annon_struc_mem*>(reinterpret_cast<copy_assign_interf*>(basic.extra->target_raw)))
		var = &pstr->annonstruct;

	if (var && !var->front().pllvmtype)
		fixupstructype(var);

	return var;
}

llvm::Type* buildllvmtypefull(std::list<type>& refdecltypevector, bool ptrdeep) {
	llvm::Type* pcurrtype = nullptr;

	//refdecltypevector.clear();

	//bool bjastypedef = false;

	std::array  lambdas = {
		std::function{[&](std::list<type>::reverse_iterator type) {
			switch (stringhash(type->spec.basicdeclspec.basic[1].c_str())) {
			case "short"_h:
				pcurrtype =
					dyn_cast<llvm::Type> (getInt16Ty((*llvmctx)));
				break;
				break;
			label_int:
			case "int"_h:
			case "long"_h:
				if (type->spec.basicdeclspec.longspecsn > 1) {
					pcurrtype = dyn_cast<llvm::Type> (getInt128Ty((*llvmctx)));
				}
				else if(type->spec.basicdeclspec.longspecsn == 1)  {
					//case "__int64"_h:
					pcurrtype = dyn_cast<llvm::Type> (getInt64Ty((*llvmctx)));
				}
				else
					pcurrtype = dyn_cast<llvm::Type> (getInt32Ty((*llvmctx)));
				break;
				break;
			case "[[nbitint]]"_h:
				pcurrtype = dyn_cast<llvm::Type> (llvm::Type::getIntNTy((*llvmctx), type->spec.basicdeclspec.longspecsn));
				break;
				break;
		addchar:
		case "_Bool"_h:
		case "char"_h:
			pcurrtype =
				dyn_cast<llvm::Type> (llvm::Type::getInt8Ty((*llvmctx)));
			break;
			break;
		case "double"_h:
		case "float"_h:
			pcurrtype =
				dyn_cast<llvm::Type> (llvm::Type::getFloatingPointTy((*llvmctx), getfltsemfromtype(*type)));
			break;
			break;
		default:
			switch (
				stringhash(type->spec.basicdeclspec.basic[0].c_str())) {
			case "union"_h:
			case "struct"_h: {
				auto currstruct = getstructorunion(type->spec.basicdeclspec);
				if (!currstruct) {
					//bincompletetype = true;
					assert("Can't find struct");
					goto addchar;
				}
				pcurrtype =
					currstruct
					->front()
					.pllvmtype;
			}
				break;
			case "enum"_h:
				throw std::logic_error{ "enum should have int type" };
			default: { // typedef
				//bjastypedef = true;
				pcurrtype = obtainvalbyidentifier(type->spec.basicdeclspec.basic[3], false, true).value()->requestType();
				return false;
			}
			}
		}
			return true;
	}},
	std::function{[&](std::list<type>::reverse_iterator type) {
		pcurrtype = dyn_cast<llvm::Type> (pcurrtype ? pcurrtype->getPointerTo() : llvm::PointerType::get((*llvmctx), 0));
		return false;
	}},
	std::function{[&](std::list<type>::reverse_iterator type) {
		pcurrtype = dyn_cast<llvm::Type> (
			llvm::ArrayType::get(pcurrtype, type->spec.array.nelems));
		return true;
	}},
	std::function{[&](std::list<type>::reverse_iterator type) {
		std::vector<llvm::Type*> paramtype;
		for (auto& a : type->spec.func.parametertypes_list.front())
			paramtype.push_back(a.requestType());
		pcurrtype = dyn_cast<llvm::Type> (llvm::FunctionType::get(
			pcurrtype, paramtype, type->spec.func.bisvariadic));
		return true;
	}} };

	try {
		for (auto typeiter = ptrdeep ? refdecltypevector.rbegin() :
			std::make_reverse_iterator(++std::find_if(refdecltypevector.begin(), refdecltypevector.end(),
				[&](::type& type) {
					return _Ranges::contains(std::array{ ::type::BASIC, ::type::POINTER }, type.uniontype);
				})); typeiter != refdecltypevector.rend(); ++typeiter) {
			if ((typeiter->cachedtype, false) || (!lambdas[typeiter->uniontype](typeiter), false))
				pcurrtype = typeiter->cachedtype;
			else
				typeiter->cachedtype = pcurrtype;
		}
	}
	catch (std::nullptr_t exc) {
		return exc;
	}

	//bincompletetype = false;

	return pcurrtype;
}


DLL_EXPORT void reset_state() {
	scopevar.resize(1);
	currtypevectorbeingbuild.resize(1);
	structorunionmembers.resize(1);
	enums.resize(1);
	scopevar.resize(1);
	pcurrblock.clear();
}


THREAD_LOCAL extern std::list<llvm::BasicBlock*> pcurrblock;

void finalizedecl();

THREAD_LOCAL static std::list<std::pair<llvm::SwitchInst*, llvm::BasicBlock*>> currswitch;

llvm::BranchInst* splitbb(const char* identifier, size_t szident);

DLL_EXPORT void beginscope() {
	bool beginofafnuc = scopevar.size() == 1;
	if (beginofafnuc) {
		currfunc = --currtypevectorbeingbuild.back().p->end();
		std::cout << "begin func at @" << currfunc->identifier << std::endl;
		var current_arg;
		auto currfuncval = currfunc->requestValue();
		auto iter_params = currfunc->type.front()
			.spec.func.parametertypes_list.front()
			.begin();
		for (auto& arg : dyn_cast<llvm::Function> (currfuncval)->args())
			iter_params++->value = &arg;

		llvmsub = llvmdibuilder->createFunction(llvmcu->getFile(), currfunc->identifier, currfunc->linkage, llvmcu->getFile(), evalperlexpruv("pos()"), llvm::DISubroutineType::get(*llvmctx, llvm::DINode::DIFlags::FlagZero, llvm::dwarf::CallingConvention::DW_CC_normal, llvm::DITypeRefArray{}), evalperlexpruv("pos()"), llvm::DINode::DIFlags::FlagZero, llvm::DISubprogram::toSPFlags(false, true, false));
			//llvm::DISubprogram::getDistinct(*llvmctx, llvmcu->getFile(), currfunc->identifier, currfunc->linkage, llvmcu->getFile(), 0, nullptr, 0, nullptr, 0, 0, llvm::DINode::DIFlags::FlagZero, llvm::DISubprogram::toSPFlags(false, true, false), llvmcu);
		dyn_cast<llvm::Function> (currfuncval)->setSubprogram(llvmsub);
	}

	splitbb("", 0);
	//pcurrblock.push_back (llvm::BasicBlock::Create (
	//(*llvmctx), "", dyn_cast<llvm::Function> (currfunc->pValue)));
	//llvmbuilder->SetInsertPoint (pcurrblock.back ());
	scopevar.push_back({});
	currtypevectorbeingbuild.push_back(
		{ --scopevar.end(), currdecltypeenum::NORMAL });

	var OrigParamValue;

	if (beginofafnuc)
		for (auto& param : currfunc->type.front().spec.func.parametertypes_list.front()) {
			auto origparamvalue = param.value;

			printvaltype(val{ valbase{param} });

			param.firstintroduced = pcurrblock.back();

			addvar(param);

			printvaltype(val{ valbase{param} });

			llvmbuilder->CreateStore(origparamvalue, param.value);
		}

	structorunionmembers.push_back({});

	enums.push_back({});

	std::cout << "begin scope finished" << std::endl;
}

void fixuplabels();

DLL_EXPORT void endreturn(std::unordered_map<unsigned, std::string>&& hashes);

DLL_EXPORT void dumpmodule();

DLL_EXPORT void probemodule() {
	if (scopevar.size() == 1) {
		llvm::raw_null_ostream ostr{};
		llvm::AssemblyAnnotationWriter wrt{};
		mainmodule->print(ostr, &wrt);
	}
}

DLL_EXPORT void endscope() {
	// nonconstructable.mainmodule.
	// endexpression();
	//pcurrblock.pop_back();
	scopevar.pop_back();
	if (scopevar.size() > 1)
		splitbb("", 0);

	currtypevectorbeingbuild.pop_back();
	structorunionmembers.pop_back();
	enums.pop_back();

	if (scopevar.size() == 1) { //end of a function
		if (!bareweinabrupt())
			endreturn({});
		pcurrblock.pop_back();
		fixuplabels();
		currfunc = empty_func.begin();
		llvmsub = nullptr;
	}

	//probemodule();
	/*dumpmodule();
	dyn_cast<llvm::Function>(currfunc->value)->eraseFromParent();*/
}

DLL_EXPORT void endexpression() { phndl->immidiates.resize(1); }

THREAD_LOCAL std::list<llvm::BasicBlock*> dowhileloops;

THREAD_LOCAL std::list<std::list<llvm::BranchInst*>> breakbranches;

THREAD_LOCAL std::list<std::list<llvm::BranchInst*>> continuebranches;

void fixupcontinuebranches(), fixupbrakebranches();

DLL_EXPORT void startdowhileloop() {
	splitbb("", 0);

	dowhileloops.push_back(pcurrblock.back());
	breakbranches.push_back({});
	continuebranches.push_back({});
}

DLL_EXPORT void enddowhileloop() {
	fixupcontinuebranches();
	startifstatement();
	fixupbrakebranches();
	ifstatements.back().first[0]->setSuccessor(1, pcurrblock.back());
	ifstatements.back().first[0]->setSuccessor(0, dowhileloops.back());
	ifstatements.back().second->eraseFromParent();
	ifstatements.pop_back();
	dowhileloops.pop_back();
}

DLL_EXPORT void addbreak() {
	breakbranches.back().push_back(llvmbuilder->CreateBr(pcurrblock.back()));
}

DLL_EXPORT void addcontinue() {
	continuebranches.back().push_back(llvmbuilder->CreateBr(pcurrblock.back()));
}

void fixupbrakebranches() {
	for (auto branch : breakbranches.back())
		branch->setSuccessor(0, pcurrblock.back());

	breakbranches.pop_back();
}

void fixupcontinuebranches() {
	for (auto branch : continuebranches.back())
		branch->setSuccessor(0, pcurrblock.back());

	continuebranches.pop_back();
}

THREAD_LOCAL std::list<std::array<llvm::BasicBlock*, 2>> forloops;

DLL_EXPORT void startforloopcond() {
	std::array<llvm::BasicBlock*, 2> bb;
	splitbb("", 0);
	bb[0] = pcurrblock.back();

	forloops.push_back(bb);
	breakbranches.push_back({});
	continuebranches.push_back({});
}

DLL_EXPORT void endforloopcond() {
	if (immidiates.size() == 1) {
		insertinttoimm("1", sizeof "1" - 1, "", 0, 3);
	}
	startifstatement();
	endexpression();
	//insertinttoimm("0", sizeof "0" - 1, "", 0, 3);
	//startifstatement();
	auto lastblcok = pcurrblock.back();

	forloops.back()[1] = lastblcok;
}

DLL_EXPORT void addforloopiter() {
	llvmbuilder->CreateBr(forloops.back()[0]);
	splitbb("", 0);

	//endifstatement();
	ifstatements.back().first[0]->setSuccessor(0, pcurrblock.back());
}

DLL_EXPORT void endforloop() {
	fixupcontinuebranches();
	llvmbuilder->CreateBr(forloops.back()[1]);
	forloops.pop_back();
	//endifstatement();
	splitbb("", 0);
	fixupbrakebranches();
	ifstatements.back().first[0]->setSuccessor(1, pcurrblock.back());
	ifstatements.back().second->eraseFromParent();
	ifstatements.pop_back();
}

val decay(val lvalue, bool bfunonly) {
	auto& currtype = lvalue.type;
	auto elemtype = lvalue.requestType();

	if ((currtype.front().uniontype == type::ARRAY && !bfunonly)
		|| currtype.front().uniontype == type::FUNCTION) {
		::type ptrtype{ ::type::POINTER };

		if (currtype.front().uniontype == type::ARRAY)
			currtype.erase(currtype.begin());
		currtype.push_front(ptrtype);

		assert(currtype.front().uniontype == ::type::POINTER);


		lvalue.value = lvalue.lvalue;

		lvalue.lvalue = nullptr;

	}
	return lvalue;
}

DLL_EXPORT void startfunctioncall() {
	callees.push_back(--immidiates.end());
}

THREAD_LOCAL std::list<std::pair<llvm::BranchInst*, std::string>> branches;

llvm::BranchInst* splitbb(const char* identifier, size_t szident) {
	bool bareweabrupt = bareweinabrupt();
	if (pcurrblock.size())
		pcurrblock.pop_back();
	else
		bareweabrupt = true;
	pcurrblock.push_back(llvm::BasicBlock::Create(
		(*llvmctx), std::string{ identifier, szident }, dyn_cast<llvm::Function> (currfunc->requestValue())));
	llvm::BranchInst* preturn=nullptr;
	if (!bareweabrupt)
		preturn = llvmbuilder->CreateBr(pcurrblock.back());
	llvmbuilder->SetInsertPoint(pcurrblock.back());
	return preturn;
}

DLL_EXPORT void splitbb(std::unordered_map<unsigned, std::string>&& hashes) {
	splitbb(STRING_TO_PTR_AND_SZ(hashes["lbl"_h]));
}

DLL_EXPORT void gotolabel(std::unordered_map<unsigned, std::string>&& hashes) {
	branches.push_back({ llvmbuilder->CreateBr(pcurrblock.back()), hashes["gtid"_h] });
}

void fixuplabels() {
	for (auto& [branchinst, ident] : branches)
		for (auto& bb : *dyn_cast<llvm::Function> (currfunc->requestValue()))
			if (bb.getName() == ident)
				branchinst->setSuccessor(0, &bb);
	branches.clear();
}

DLL_EXPORT void startswitch() {
	//pcurrblock.pop_back();
	//pcurrblock.push_back(llvm::BasicBlock::Create((*llvmctx), "", dyn_cast<llvm::Function> (currfunc->pValue)));
	auto& imm = immidiates.back();
	imm = phndl->requireint(imm);
	auto dummyblock = llvm::BasicBlock::Create((*llvmctx), "", dyn_cast<llvm::Function> (currfunc->requestValue()));
	currswitch.push_back({ llvmbuilder->CreateSwitch(imm.value, dummyblock), dummyblock });
	breakbranches.push_back({});

	//llvmbuilder->SetInsertPoint(pcurrblock.back());
	phndl->immidiates.pop_back();
}

bool bareweinabrupt(bool barewe) {
	/*static bool bareweinabrupt;
	bool bareweinabruptlast = bareweinabrupt;
	bareweinabrupt = barewe;*/
	if (pcurrblock.size())
		if (pcurrblock.back()->size()) {
			auto lastinstropcode = pcurrblock.back()->back().getOpcode();
			return _Ranges::contains(std::array{ llvm::Instruction::Br, llvm::Instruction::Switch,llvm::Instruction::Ret }, lastinstropcode);
		}
		else
			return false;
	return true;
}

DLL_EXPORT void endswitch() {
	splitbb("", 0);
	fixupbrakebranches();
	if (currswitch.back().first->getDefaultDest() == currswitch.back().second)
		currswitch.back().first->setDefaultDest(pcurrblock.back());
	currswitch.back().second->eraseFromParent();
	currswitch.pop_back();
}

DLL_EXPORT void addCase() {
	splitbb("", 0);
	auto &lastval = phndl->immidiates.back();

	auto val = getConstantIntegerValue(lastval);

	lastval.constant = llvm::ConstantInt::get(currswitch.back().first->getCondition()->getType(), val, lastval.type.front().spec.basicdeclspec.basic[0] != "unsigned");
	
	currswitch.back().first->addCase(llvm::dyn_cast<llvm::ConstantInt> (lastval.constant), pcurrblock.back());
	phndl->immidiates.pop_back();
}

DLL_EXPORT void addDefaultCase() {
	splitbb("", 0);
	currswitch.back().first->setDefaultDest(pcurrblock.back());
}

/*val<> getfunctionptr(val<> fptr) {
	for(auto a = fptr.type.begin(); a != fptr.type.end(); ++a)
		if(a->uniontype == type::FUNCTION) break;
		else fptr.type.erase(a), fptr.value = llvmbuilder->CreatePointerCast
(value, type->getPointerTo ())
}*/

llvm::Value* floattodoubleifneeded(llvm::Value* possiblefloat) {
	if (possiblefloat->getType()->isFloatTy() && allowccompat)
		return llvmbuilder->CreateFPCast(possiblefloat, llvm::Type::getFloatingPointTy((*llvmctx), llvm::APFloatBase::IEEEdouble()));
	return possiblefloat;
}

DLL_EXPORT void endfunctioncall() {
	auto lastblock = pcurrblock.back();

	auto argsiter = callees.back();

	auto calleevalntype = *argsiter;

	callees.pop_back();

	++argsiter;

	type fntype{ type::FUNCTION };

	fntype.spec.func.bisvariadic = true;

	if (!is_type_function_or_fnptr(calleevalntype.type)) {

		type ptrtype{ type::POINTER };

		calleevalntype = convertTo(calleevalntype, { ptrtype, fntype, basicint });
	}

	//assert(calleevalntype.value->getType()->isPointerTy());

	if (calleevalntype.type.front().uniontype != type::POINTER) {

		std::list<std::pair<std::list<::var>::reverse_iterator, int>> revfunsrank;

		std::list<::var>::reverse_iterator iter;

		while (auto val = obtainvalbyidentifier(calleevalntype.identifier, false, false, true)) {
			iter = val.value();
			if(iter->type.front().uniontype == type::FUNCTION)
				revfunsrank.push_back({ iter, 0 });
		}

		reset_obtainvalbyidentifier_search();

		if (revfunsrank.size() <= 1)
			goto rest;

		//revfuns.remove_if([](std::list<::var>::reverse_iterator& a) { return a->type.front().spec.func.parametertypes_list.size() != callees.size(); });

		const auto distance = (long long)std::distance(argsiter, ::immidiates.end());

		constexpr auto maxparamindividualscore = 2;

		for (auto &funccand : revfunsrank) {

			funccand.second = distance * maxparamindividualscore + std::abs(distance - (long long)funccand.first->type.front().spec.func.parametertypes_list.front().size());

			auto argsiterarg = argsiter;
			
			for (auto& params : funccand.first->type.front().spec.func.parametertypes_list.front()) {
				if (::immidiates.end() == argsiterarg) break;
				const bool decayarr = params.type.front().uniontype == type::POINTER && argsiterarg->lvalue;
				auto argval = decay(*argsiterarg, decayarr);
				if (params.type.front().uniontype != argval.type.front().uniontype) {
					funccand.second += 2;
				}
				else if (params.type.front().uniontype == type::POINTER) {
					if (!comparetwotypesdeep(params.type, argval.type)) {
						funccand.second += 1;
					}
				}
				else if (bIsBasicFloat(params.type.front()) != bIsBasicFloat(argval.type.front())) {
					funccand.second += 1;
				}

				argsiterarg++;
			}
		}

		revfunsrank.sort([](std::pair<std::list<::var>::reverse_iterator, int>& arg, std::pair<std::list<::var>::reverse_iterator, int>& arg2) {
			return arg.second < arg2.second;
			});

		revfunsrank.front().first->requestValue();

		val imm{ *revfunsrank.front().first };

		calleevalntype = imm;
	}
	else {
		calleevalntype.type.pop_front();
	}

rest:

	/*{
		std::list newttype = { fntype };

		newttype.splice(newttype.end(), calleevalntype.type, ++calleevalntype.type.begin(), calleevalntype.type.end());

		calleevalntype.type = std::move(newttype);
	}*/

	llvm::Value* callee = calleevalntype.value;

	/*std::string type_str;
	llvm::raw_string_ostream rso (type_str);
	calleevalntype.value->getType ()->print (rso);
	std::cout << calleevalntype.value->getName ().str () << " is " << rso.str ()
			  << std::endl;*/

	auto functype = calleevalntype.requestType();

	llvm::Value* pval;

	llvmbuilder->SetInsertPoint(lastblock);

	std::vector<llvm::Value*> immidiates;

	auto& verylongthingy = calleevalntype.type.front().spec.func.parametertypes_list.front();

	auto iterparams = verylongthingy.begin();

	bool breached = false;

	std::transform(
		argsiter, ::immidiates.end(), std::back_inserter(immidiates),
		[&](basehndl::val elem) { 
			auto iterparamslast = iterparams++;
			breached = breached || iterparamslast == verylongthingy.end();
			if (!breached) {
				const bool decayarr = iterparamslast->type.front().uniontype == type::POINTER && elem.lvalue;
				return convertTo(elem, iterparamslast->type, decayarr).value;
			}
			return floattodoubleifneeded(decay(elem).value);
		}
	);

	::immidiates.erase(--argsiter, ::immidiates.end());

	printvaltype(calleevalntype);

	val fixupval = calleevalntype;

	if(fixupval.type.front().spec.func.callconv.empty() && !allowccompat)
		fixupval.type.front() = fntype;

	// if (functype->isPtrOrPtrVectorTy ())
	pval = llvmbuilder->CreateCall(
		llvm::dyn_cast<llvm::FunctionType> (
			fixupval.requestType()),
		callee, immidiates);
	// else
	// pval = llvmbuilder->CreateCall (
	// llvm::dyn_cast<llvm::Function> (callee)->getFunctionType (),
	// llvm::dyn_cast<llvm::Value> (callee), immidiates);

	calleevalntype.type.pop_front();

	phndl->immidiates.push_back(
		val{ calleevalntype.type, pval });
}

DLL_EXPORT void endreturn(std::unordered_map<unsigned, std::string>&& hashes) {
	//llvmbuilder->SetInsertPoint (pcurrblock.back ());
	if (hashes.contains("returnval"_h)) {
		auto currfunctype = currfunc->type;
		currfunctype.pop_front();
		auto op = convertTo(immidiates.back(), currfunctype, currfunctype.front().uniontype == type::POINTER && immidiates.back().lvalue);
		llvmbuilder->CreateRet(op.value);
	}
	else {
		insertinttoimm("0", sizeof "1" - 1, "", 0, 3);
		endreturn({ {"returnval"_h, "0"} });
	}
}

DLL_EXPORT void endfunctionparamdecl(std::unordered_map<unsigned, std::string>&& hashes) {

	//for (auto& a : *currtypevectorbeingbuild.back().p)
	//	a.pllvmtype = buildllvmtypefull(a.type);

	currtypevectorbeingbuild.pop_back();

	auto& functype = currtypevectorbeingbuild.back().p->back().type.back();

	assert(functype.uniontype == type::FUNCTION);

	functype.spec.func.bisvariadic = hashes.contains("rest"_h);
}

DLL_EXPORT void addptrtotype(std::unordered_map<unsigned, std::string>&& hashes);

DLL_EXPORT void endqualifs(std::unordered_map<unsigned, std::string>&& hashes) {
	auto& lastvar = currtypevectorbeingbuild.back().p->back();

	auto& refbasic = lastvar.type.back().spec.basicdeclspec.basic;

	if (std::all_of(refbasic.begin(), refbasic.end(), (bool (*)( const std::string& c ))std::empty))
		if (pcurrblock.empty()) refbasic[1] = "int";
		else throw std::runtime_error{ "decl with no basic info" };

	if (_Ranges::contains(std::array{ "struct", "union", "enum" }, refbasic[0]))
		switch (stringhash(refbasic[0].c_str())) if (0);
		else if(0) {
			case "struct"_h:
			case "union"_h:
				if (refbasic[3].empty()) {
					auto* reflaststruc = &*laststruc;
					//if (!reflaststruc->back().pllvmtype) fixupstructype(reflaststruc);
					auto extraptr = lastvar.type.back().spec.basicdeclspec.extra = std::make_shared<extra_basic_union>();
					extraptr->~extra_basic_union();
					new (extraptr->target_raw) annon_struc_mem{};
					reinterpret_cast<annon_struc_mem*>(extraptr->target_raw)->annonstruct = *reflaststruc;
				}
		}
		else if (0) {
			case "enum"_h:
				lastvar.type.back() = basicint ;
		}
							/*					  else
							if (0) case "enum"_h:
						{
							lastvar.type.back().spec.basicdeclspec.pexternaldata = &enums.back().back();
						}*/
						//currtypevectorbeingbuild.pop_back();

	/*if (lastvar.type.front().uniontype == type::FUNCTION) {
		lastvar.requestValue();
	}*/
}

DLL_EXPORT void announce_decl() {
	auto& lastvar = currtypevectorbeingbuild.back().p->back();

	if (pcurrblock.empty() && currtypevectorbeingbuild.back().currdecltype != currdecltypeenum::STRUCTORUNION
		&& currtypevectorbeingbuild.back().currdecltype != currdecltypeenum::PARAMS) {
		if (lastvar.linkage.empty()) {
			lastvar.requestValue();
		}
		auto idtostore = callstring("getidtostor", lastvar.identifier.c_str(), lastvar.identifier.length());
		assert(idtostore != -1);
		auto vartopush = lastvar;
		vartopush.seralise();
		vartopush.linkage = vartopush.linkage != "typedef" ? "extern" : vartopush.linkage;
		{
			std::unique_lock lck{ boradcastingscope };
			scopevars_global[stringhash(lastvar.identifier.c_str())][idtostore] = std::move(vartopush);
		}
		callint("broadcastid", idtostore, lastvar.identifier.c_str(), lastvar.identifier.size());
	}
}

DLL_EXPORT void startfunctionparamdecl() {

	if (currtypevectorbeingbuild.back().currdecltype ==
		currdecltypeenum::PARAMS
		&& currtypevectorbeingbuild.back().p->back().type.size() == 1)

		addptrtotype(std::unordered_map<unsigned, std::string>{});

	currtypevectorbeingbuild.back().p->back().type.push_back(
		{ type::FUNCTION });
	if (!callingconv.empty()) {
		currtypevectorbeingbuild.back().p->back().type.back().spec.func.callconv = callingconv.back();

		callingconv.pop_back();
	}

	currtypevectorbeingbuild.push_back(
		{ currtypevectorbeingbuild.back()
			 .p->back()
			 .type.back()
			 .spec.func.parametertypes_list.begin(),
		 currdecltypeenum::PARAMS });
}

DLL_EXPORT void addsubtotype(std::unordered_map<unsigned, std::string>&& hashes) {

	type arraytype{ type::ARRAY };

	auto res = llvm::dyn_cast<llvm::ConstantInt> (
		hndlcnstexpr.immidiates.back().value);

	arraytype.spec.array.nelems = *res->getValue().getRawData();
	//arraytype.spec.array.qualifiers[0] = hashes["abstrsubqualifs"_h] == "static";
	currtypevectorbeingbuild.back().p->back().type.push_back(arraytype);

	hndlcnstexpr.immidiates.pop_back();
}

DLL_EXPORT void addptrtotype(std::unordered_map<unsigned, std::string>&& hashes) {

	type ptrtype{ type::POINTER };

	ptrtype.spec.ptrqualifiers =
		parsequalifiers(hashes["qualifptr"_h]);

	currtypevectorbeingbuild.back().p->back().type.push_back(ptrtype);
}

DLL_EXPORT void setcallconv() {
	callingconv.push_back("__stdcall");
}

DLL_EXPORT void insertinttoimm(const char* str, size_t szstr, const char* suffix, size_t szstr1, int type) {
	phndl->insertinttoimm(str, szstr, suffix, szstr1, type);
}

DLL_EXPORT void subscript() {
	if (!phndl->subscripttwovalues()) {
		auto& imm = *----immidiates.end();
		imm.value = imm.lvalue;
		imm.lvalue = nullptr;
		imm.type = { {type::POINTER}, unsch };
		phndl->subscripttwovalues();
	}
}

THREAD_LOCAL static basehndl* (*phpriorhndlfn_cnst_expr)(basehndl*);

DLL_EXPORT void beginconstantexpr() {
	//cnstexpriterstart = phndl->immidiates.end();
	szcnstexprinitial = phndl->immidiates.size();

	phpriorhndlfn_cnst_expr = phndl->getrestorefn();

	//phndl = &hndlcnstexpr;

	phndl->~basehndl();

	phndl = new (phndl) handlecnstexpr{};
}

DLL_EXPORT void endconstantexpr() {
	//assert(szcnstexprinitial == phndl->immidiates.size());

	// auto res = dyn_cast<llvm::ConstantInt>(immidiates.back());

	// hndlcnstexpr.immidiates.pop_back();

	// std::cout << "computed value: " << *res->getValue().getRawData() <<
	// std::endl;
	phndl->~basehndl(),
		phndl = phpriorhndlfn_cnst_expr(phndl);
}

DLL_EXPORT unsigned docall(const char*, size_t, void*);

decltype(getInt16Ty) getfnbynbits(int nbits) {
	{
		switch (nbits) if (0)
			case 8:
				return llvm::IntegerType::getInt8Ty;
		else if (0)
			case 16:
				return llvm::IntegerType::getInt16Ty;
		else if (0)
			case 32:
				return llvm::IntegerType::getInt32Ty;
		else if (0)
			case 64:
				return llvm::IntegerType::getInt64Ty;
		else if (0)
			case 128:
				return llvm::IntegerType::getInt128Ty;
	}
	throw std::logic_error{ "unsupported integer type" };
}

/*#include <pthread.h>

static pthread_mutex_t mutexshared;
static pthread_mutexattr_t mutexsharedattr;*/

const auto initthreadmods = []{
	_scopevar = &scopevar;
	_structorunionmembers = &structorunionmembers;
	_enums = &enums;
	return nullptr;
}();
static std::mutex syncf;
static std::list<std::pair<unsigned, decltype(scopevar)::value_type>> consumablescopevars;
static std::list<std::pair<unsigned, decltype(structorunionmembers)::value_type>> consumablestructorunionmembers;
static std::list<std::pair<unsigned, decltype(enums)::value_type>> consumableenums;

static THREAD_LOCAL decltype(scopevar)::value_type::iterator consumablescopevarstopushlast;
static THREAD_LOCAL decltype(structorunionmembers)::value_type::iterator structorunionmemberstopushlast;
static THREAD_LOCAL decltype(enums)::value_type::iterator enumstopushlast;

void llvminit_thread();

DLL_EXPORT void llvminit() {
	if(getenv("SILENT"))
		std::cout.rdbuf(NULL);
	if(getenv("INTPROM"))
		allowccompat = atoi(getenv("INTPROM"));
	if(getenv("DEBUG"))
		allowdebug = atoi(getenv("DEBUG"));
	//llvminit_thread();

	static const char* inttynames[] = { "Int16", "Int32", "Int64", "Int128" };

	const char** currtyname = inttynames;

	for (auto pfun : std::array{ &getInt16Ty, &getInt32Ty, &getInt64Ty, &getInt128Ty })
		if (const char* nbits = getenv(*currtyname++)) {
			*pfun = getfnbynbits(atoi(nbits));
		}

	if (const char *triple = getenv("TRIPLE")) {
		ptriple = new llvm::Triple{triple};
	}
}

void llvminit_thread() {
	currtypevectorbeingbuild = { {scopevar.begin(), currdecltypeenum::NORMAL} };
}

DLL_EXPORT void broadcast(unsigned thrid, unsigned pos) {
	//scopevars_global[pos] = {scopevar.front(), structorunionmembers.front()};

	static std::mutex boradcastingstrc;
	static std::mutex boradcastingscope;

	//std::unique_lock lck{all};

	THREAD_LOCAL static bool hasboolintied = false;
	THREAD_LOCAL static bool hasboolintiedscope = false;

	//boradcastingscope.lock();

	for(auto first = hasboolintiedscope ? ++consumablescopevarstopushlast : scopevar.front().begin();  first != scopevar.front().end(); ++first) {
		if(!first->identifier.empty()) {
			std::unique_lock lck{boradcastingscope};
			scopevars_global[pos][stringhash(first->identifier.c_str())] = *first;
		}
	}

	//boradcastingscope.unlock();

	hasboolintiedscope = !scopevar.front().empty();

	consumablescopevarstopushlast = --scopevar.front().end();

	//boradcastingstrc.lock();

	for(auto first = hasboolintied ? ++structorunionmemberstopushlast : structorunionmembers.front().begin();  first != structorunionmembers.front().end(); ++first) {
		if(!first->front().identifier.empty()) {
			std::unique_lock lck{boradcastingstrc};
			structorunionmembers_global[pos][stringhash((first->front().type.front().spec.basicdeclspec.basic[0] + " " + first->front().identifier).c_str())] = *first;
		}
	}

	//boradcastingstrc.unlock();

	hasboolintied = !structorunionmembers.front().empty();

	structorunionmemberstopushlast = --structorunionmembers.front().end();
	
	/*if (thrid, true) {
		//printf("setting pos %d\n", pos);
		//std::unique_lock lck{maskchn};
		//scopevars_state.set(pos);
		//maskchncondvar.notify_all();
	}*/
}

DLL_EXPORT void flushfilescopes(unsigned n, unsigned id) {
	static bool storedscopevar = false;
	static bool storedsstructs = false;
	static bool storedsenums = false;
	for (auto i : _Ranges::iota_view<unsigned, unsigned>(0u, n)) {
		syncf.lock();
		consumablescopevars.push_back({id, {storedscopevar ? ++consumablescopevarstopushlast : scopevar.front().begin(), scopevar.front().end()}});
		consumablestructorunionmembers.push_back({id, {storedsstructs ? ++structorunionmemberstopushlast : structorunionmembers.front().begin(), structorunionmembers.front().end()}});
		//consumableenums.push_back({id, {storedsenums ? ++enumstopushlast : enums.front().begin(), enums.front().end()}});

		syncf.unlock();
	}
	syncf.lock();
	storedscopevar = scopevar.size() > 0;
	consumablescopevarstopushlast = --scopevar.front().end();
	storedsstructs = consumablestructorunionmembers.size() > 0;
	structorunionmemberstopushlast = --structorunionmembers.front().end();
	syncf.unlock();
	//storedsenums = enums.size() > 0;
	//enumstopushlast = --enums.front().end();
}


DLL_EXPORT void startmodule(const char* modulename, size_t szmodulename) {
	/*pthread_mutexattr_init(&mutexsharedattr);
	pthread_mutexattr_setpshared(&mutexsharedattr, 1);
	pthread_mutex_init(&mutexshared, &mutexsharedattr);*/
	llvminit_thread();
	static THREAD_LOCAL llvm::LLVMContext llvmctxobj{};
	llvmctx = &llvmctxobj;
	static THREAD_LOCAL llvm::IRBuilder llvmbuilderobj{llvmctxobj};
	llvmbuilder = &llvmbuilderobj;
	static THREAD_LOCAL llvm::Module llvmmainmodobj{modname = std::string{modulename, szmodulename}, (*llvmctx)};
	mainmodule = &llvmmainmodobj;

	auto pdifile = llvm::DIFile::get(*llvmctx, std::string{modulename, szmodulename}, "");

	static THREAD_LOCAL llvm::DIBuilder llvmdibuilderobj{llvmmainmodobj};
	llvmdibuilder = &llvmdibuilderobj;
	
	llvmcu = llvmdibuilder->createCompileUnit(llvm::dwarf::DW_LANG_C, llvmdibuilder->createFile(std::string{modulename, szmodulename}, "/"), "regularc", false, "", 0);

	(*llvmctx).setOpaquePointers(true);

	if (ptriple)
		mainmodule->setTargetTriple(ptriple->getTriple());

	if (datalayout_str) {
		pdatalayout = new llvm::DataLayout{ datalayout_str };
		mainmodule->setDataLayout(*pdatalayout);
	}
	else {
		pdatalayout = new llvm::DataLayout{mainmodule};
	}

	mainmodule->addModuleFlag(llvm::Module::Warning, "Debug Info Version",
                           llvm::DEBUG_METADATA_VERSION);

	//mainmodule->addModuleFlag(llvm::Module::Warning, "Dwarf Version", llvm::dwarf::DWARF_VERSION);

	/*if (const char* preplaypath = getenv("REPLAY")) {
		std::ifstream replay{ preplaypath, std::ifstream::binary };

		unsigned int hash;

		std::string value;

		std::unordered_map<unsigned, std::string> map;

		do {
			std::getline(replay, value, '\0');

			if (!value.empty()) {
				replay.read((char*)&hash, 4);
				map.insert({ hash, value });
			}
			else {
				std::getline(replay, value, '\0');
				docall(value.c_str(), value.length(), &map);
				map.clear();
			}
		} while (!replay.eof());
	}

	_mainmodule = &mainmodule;
	_scopevar = &scopevar;
	_structorunionmembers = &structorunionmembers;
	_enums = &enums;
	_llvmctx = &llvmctx;
	_llvmbuilder = &llvmbuilder;*/

	//system("PAUSE");
}

#include <condition_variable>
#include <mutex>

static std::condition_variable condwake;
static std::mutex mutexwork;

static bool endwork = false;

//extern "C" pthread_t thread;

std::ofstream record{ getenv("RECORD") ? getenv("RECORD") : "", std::ios::binary };

DLL_EXPORT void endmodule();
#include <setjmp.h>
extern "C" THREAD_LOCAL_C jmp_buf docalljmp;
extern "C" THREAD_LOCAL_C int areweinuser;
DLL_EXPORT void endmoduleabrupt() {
	areweinuser = 1;
	if (!exc_setjmp(docalljmp, 1)) {
		if (scopevar.front().size()) if (auto& fun = scopevar.front().back(); fun.type.front().uniontype == type::FUNCTION) {
			if (fun.value) if (auto llvmfun = dyn_cast<llvm::Function>(fun.value);
				!llvmfun->isDeclaration()) {
				llvmfun->deleteBody();
			}
		}
	}
	areweinuser = 0;
	endmodule();
}

DLL_EXPORT void dumpmodule();

DLL_EXPORT void endmodule() {
	dumpmodule();
	//areweinuser = 1;
	//if (!sigsetjmp(docalljmp, 1)) {
		//llvmbuilder.release();
		//mainmodule.release();
		//llvmctx.release();
	//}
	//areweinuser = 0;
	return;

	//endmoduleabrupt();
}

extern "C" THREAD_LOCAL_C unsigned int matchpos;

DLL_EXPORT void dumpmodule() {
	/*if (getenv("THREADING")) {
		mutexwork.lock();
		endwork = true;
		mutexwork.unlock();
		condwake.notify_one();
		//pthread_join(thread, nullptr);
	}*/
	//if (scopevar.front().size()) if (auto& fun = scopevar.front().back(); fun.type.front().uniontype == type::FUNCTION) {
	//	if (fun.value) if (auto llvmfun = dyn_cast<llvm::Function>(fun.value); !llvmfun->isDeclaration()) {
			/*areweinuser = 1;
			if (!sigsetjmp(docalljmp, 1)) {*/
				//pthread_mutex_lock(&mutexshared);
				std::cout << "Dumping " << mainmodule->getName().str() << " ..." << std::endl;
				std::error_code code{};
				llvm::raw_fd_ostream output{
					mainmodule->getName().str() + ".bc", code, llvm::sys::fs::CD_CreateAlways },
					outputll{ mainmodule->getName().str() + ".ll",
								code, llvm::sys::fs::CD_CreateAlways };
				if (!record.is_open()) {
					llvmdibuilder->finalize();
					mainmodule->print(outputll, nullptr);
					llvm::WriteBitcodeToFile(*mainmodule, output);
					//mainmodule->print(outputll, nullptr);
					//llvm::WriteBitcodeToFile(*mainmodule, output);
				}
			//}
			//areweinuser = 0;
		//}
		//endwork = true;
		//dyn_cast<llvm::Function>(currfunc->value)->deleteBody();
		//pthread_mutex_unlock(&mutexshared);
		//nonconstructable.mainmodule.~Module();
		//delete pdatalayout;
	//}
}
#include "llvm/Transforms/Utils/Cloning.h"
DLL_EXPORT void waitforthread() {
	std::unique_lock lock{ mutexwork };
	condwake.wait(lock);
}
DLL_EXPORT void initthread() {
	/*llvmbuilder = std::make_unique<llvm::IRBuilder<>>((*llvmctx));
	mainmodule = std::make_unique<llvm::Module>(std::string{ "" }, (*llvmctx));

	(*llvmctx).setOpaquePointers(true);
	mainmodule->setDataLayout(*pdatalayout);

	scopevar.front() = _scopevar->front();
	structorunionmembers = *_structorunionmembers;
	enums = *_enums;

	currtypevectorbeingbuild = { {scopevar.begin(), currdecltypeenum::NORMAL} };*/

	//condwake.notify_one();
}
#include <setjmp.h>
extern "C" THREAD_LOCAL_C jmp_buf docalljmp;
extern "C" THREAD_LOCAL_C bool binabrupt;
DLL_EXPORT void dumpabrupt() {
	binabrupt = true;
	auto pfn = dyn_cast<llvm::Function>(currfunc->value);
	if (pfn) {
		scopevar.pop_back();

		currtypevectorbeingbuild.pop_back();
		structorunionmembers.pop_back();
		enums.pop_back();

		pcurrblock.pop_back();
		branches.clear();
		pfn->deleteBody();
	}
	exc_longjmp(docalljmp, 1);
	/*std::error_code code{};
	llvm::raw_fd_ostream
		outputll{ std::string{nonconstructable.mainmodule.getName()} + ".ll",
				 code };
	nonconstructable.mainmodule.print(outputll, nullptr);*/
}

DLL_EXPORT void unary(std::unordered_map<unsigned, std::string>&& hashes) {
	std::string imm;

	imm.assign(hashes["unop"_h]);

	auto phpriorhndlfn = phndl->getrestorefn();

	switch (stringhash(imm.c_str())) {
	case "-"_h:
	case "+"_h:
	case "!"_h:
		if (bIsBasicFloat(phndl->immidiates.back().type.front()))
			phndl->~basehndl(),
			phndl = dynamic_cast<basehndl*>(new (phndl) handlefpexpr{});
		break;
	}

	switch (stringhash(imm.c_str())) {
	case "&"_h: {
		phndl->getaddress();
		break;
	}
	case "*"_h:
		phndl->applyindirection();
		break;
	case "~"_h:
		phndl->getbitwisenot();
		break;
	case "-"_h:
		phndl->getnegative();
		break;
	case "+"_h:
		phndl->getpositive();
		break;
	case "!"_h:
		phndl->getlogicalnot();
		break;
	}

	phndl->~basehndl();

	phndl = phpriorhndlfn(phndl);
}

DLL_EXPORT void unaryincdec(std::unordered_map<unsigned, std::string>&& hashes) {
	std::string immpostfix = hashes["postfixarithraw"_h];

	std::string imm = !immpostfix.empty() ? immpostfix : hashes["prefixarithraw"_h];

	decltype(phndl->getrestorefn()) phpriorhndl = nullptr;//phndl->getrestorefn();

	if (bIsBasicFloat(phndl->immidiates.back().type.front()))
		phpriorhndl = phndl->getrestorefn(),
		phndl->~basehndl(),
		phndl = new (phndl) handlefpexpr{};

	unsigned int type = 3; // << 2 | 2;

	auto immvalue_non_modified = immidiates.back();

	if (immvalue_non_modified.type.front().uniontype != type::POINTER &&
		!bIsBasicFloat(immvalue_non_modified.type.front()))

		immidiates.back() = phndl->requireint(immvalue_non_modified);

	insertinttoimm("1", sizeof "1" - 1, "", 0, type);

	phndl->addlasttwovalues(imm == "--", true);

	auto immvalue_modified = immidiates.back();

	immvalue_modified.identifier.append("[[modified]]");

	immidiates.insert(--immidiates.end(), immvalue_non_modified);

	phndl->assigntwovalues();

	if (!immpostfix.empty())
		immidiates.back() = immvalue_non_modified;
	if (phpriorhndl)
		phndl->~basehndl(),

		phndl = phpriorhndl(phndl);
}

DLL_EXPORT void binary(std::unordered_map<unsigned, std::string>&& hashes) {
	std::string imm;

	imm.assign(hashes["binoplast"_h]);

	auto phpriorhndl = phndl->getrestorefn();

	auto ops = std::array{ *----phndl->immidiates.end(), phndl->immidiates.back() };

	//phndl->usualarithmeticconversions(ops);

	if (bIsBasicFloat(ops[0].type.front()) || bIsBasicFloat(ops[1].type.front()))
		phndl->~basehndl(),
		phndl = dynamic_cast<basehndl*>(new (phndl) handlefpexpr{});

	const char* inttoins = "";
	bool bislogicaland;

	switch (stringhash(imm.c_str())) {
	case "*"_h:
		phndl->mlutiplylasttwovalues();
		break;
	case "/"_h:
		phndl->dividelasttwovalues();
		break;
	case "%"_h:
		phndl->modulolasttwovalues();
		break;
	case "+"_h:
		phndl->addlasttwovalues(false);
		break;
	case "-"_h:
		phndl->addlasttwovalues(true);
		break;
	case "<<"_h:
		phndl->shifttwovalues(false);
		break;
	case ">>"_h:
		phndl->shifttwovalues(true);
		break;
	case ">"_h:
		phndl->relatetwovalues(llvm::CmpInst::Predicate::ICMP_SGT,
			llvm::CmpInst::Predicate::ICMP_UGT, llvm::CmpInst::Predicate::FCMP_OGT);
		break;
	case "<"_h:
		phndl->relatetwovalues(llvm::CmpInst::Predicate::ICMP_SLT,
			llvm::CmpInst::Predicate::ICMP_ULT, llvm::CmpInst::Predicate::FCMP_OLT);
		break;
	case "<="_h:
		phndl->relatetwovalues(llvm::CmpInst::Predicate::ICMP_SLE,
			llvm::CmpInst::Predicate::ICMP_ULE, llvm::CmpInst::Predicate::FCMP_OLE);
		break;
	case ">="_h:
		phndl->relatetwovalues(llvm::CmpInst::Predicate::ICMP_SGE,
			llvm::CmpInst::Predicate::ICMP_UGE, llvm::CmpInst::Predicate::FCMP_OGE);
		break;
	case "=="_h:
		phndl->relatetwovalues(llvm::CmpInst::Predicate::ICMP_EQ,
			llvm::CmpInst::Predicate::ICMP_EQ, llvm::CmpInst::Predicate::FCMP_OEQ);
		break;
	case "!="_h:
		phndl->relatetwovalues(llvm::CmpInst::Predicate::ICMP_NE,
			llvm::CmpInst::Predicate::ICMP_NE, llvm::CmpInst::Predicate::FCMP_ONE);
		break;
	case "&"_h:
		phndl->bitwisetwovalues(llvm::Instruction::And);
		break;
	case "^"_h:
		phndl->bitwisetwovalues(llvm::Instruction::Xor);
		break;
	case "|"_h:
		phndl->bitwisetwovalues(llvm::Instruction::Or);
		break;
	case "&&"_h:
		++nbranches.back().itersecond;
		inttoins = "0";
		bislogicaland = true;
		goto mainbranch;
	case "||"_h:
		++nbranches.back().itersecond;
		(*nbranches.back().itersecond)->first[0]->swapSuccessors();
		bislogicaland = false;
		inttoins = "1";
	mainbranch: {
		auto& currbranch = nbranches.back();
		auto refarr = *nbranches.back().itersecond;
		//refarr[1]->replaceAllUsesWith(refarr[0]);
		//refarr->first[0]->swapSuccessors();

		/*auto iter = nbranches.back().first.begin();

		std::advance(iter, nbranches.back().second.size());

		(*iter)->first[1] = (llvm::BranchInst*)"0";*/

		var& ordinary = *currbranch.iterval;

		//std::rotate(nbranches.back().second.begin(), --nbranches.back().second.end(), nbranches.back().second.end());
		//++nbranches.back().second;
		phndl->logictwovalues(bislogicaland);

		immidiates.back().identifier = "[[logicop]]";

		auto lastsplit = splitbb("", 0);

		int fullindex = refarr->first[0]->getSuccessor(1) != refarr->second;
		refarr->first[0]->setSuccessor(!fullindex, pcurrblock.back());
		refarr->second->eraseFromParent();
		//ifstatements.erase(branch);

		val ordinary_imm = val{ ordinary };
		ordinary_imm.lvalue = ordinary_imm.value;

		immidiates.push_back(ordinary_imm);

		insertinttoimm(inttoins, 1, "", 0, 3);

		phndl->assigntwovalues();

		immidiates.pop_back();

		//auto iter = nbranches.back().first.begin();

		//if (nbranches.back().first.size() > 1)

			//std::advance(iter, nbranches.back().second.size());

		nbranches.back().second.push_back({ splitbb("", 0), lastsplit });

		lastsplit->setSuccessor(0, pcurrblock.back());

		auto itersecond = nbranches.back().itersecond;

		if (++itersecond == currbranch.first.end())
			currbranch.first.erase(++currbranch.first.begin(), currbranch.first.end()),
			currbranch.itersecond = currbranch.first.begin();
		//exhausted current logical ops
	//nbranches.back().second.pop_back();
		ifstatements.erase(refarr);
		}
	break;
	case "="_h:
		phndl->assigntwovalues();
		break;
	case "*="_h:
	case "/="_h:
	case "%="_h:
	case "+="_h:
	case "-="_h:
	case "<<="_h:
	case ">>="_h:
	case "&="_h:
	case "^="_h:
	case "|="_h:
		immidiates.insert(--immidiates.end(), *----immidiates.end());
		hashes["binoplast"_h].erase(--hashes["binoplast"_h].end());
		binary(std::move(hashes));
		phndl->assigntwovalues();
		break;
	}

	//opbbs.pop_back ();
	phndl->~basehndl();
	phndl = phpriorhndl(phndl);
}

void printtype(llvm::Type* ptype) { // debug purpose only
	printtype(ptype, "");
}

// llvm::BinaryOperator::CreateMul(*immidiates.begin(), *immidiates.end());
// std::cout << "base type of " << currdeclidentifier << " is typedef " <<
// !bwhich << " :" << spec << ", is declaring a typedef :" << bistypedef <<
// std::endl;

//bindings_parsing parsing;

//bindings_compiling compiling;

std::list<std::pair<std::string, void*>> recursion_list;

int lasttop = -1;

void* lastoffsetvector;

void print_tabs(int n) {
	while (n--) printf("\t");
}

void do_print_layour() {
	int n = 0;
	for (auto patt : recursion_list)
		print_tabs(n++), printf(" %s\n", patt.first.c_str());
}

DLL_EXPORT void num_lit(std::unordered_map<unsigned, std::string> &hashes) {
	unsigned int type;
	//int n = getnameloc("numberliteralraw", *ptable);

	//ntoprint[0] = getnameloc("uns", *ptable);

	//int ntoprint[2], ntoclear;

	//ntoprint[1] = getnameloc2("lng", *ptable,a,0);

	std::string groups[] = { "hex", "bin", "oct", "dec" };

	//for (const char** pgroup = groups; pgroup != 1[&groups]; ++pgroup)
	for (int i = 0; i < std::extent< decltype(groups) >::value; ++i)
	{
		//ntoclear = getnameloc3(*pgroup, *ptable, a, 0, { .dontsearchforclosest = 0 });
		//if (ntoclear != -1 && a->offset_vector[2 * ntoclear] != -1)
		std::string curr = hashes[stringhash(groups[i].c_str())];
		if (!curr.empty())
		{
			type = i; //pgroup - groups; //<< 2;//| (a->offset_vector[2 * ntoprint[0]] != -1) | (a->offset_vector[2 * ntoprint[1]] != -1) << 1;

			insertinttoimm(STRING_TO_PTR_AND_SZ(curr), STRING_TO_PTR_AND_SZ(hashes["lng"_h]), type);

			//a->offset_vector[2 * ntoclear] = a->offset_vector[2 * ntoclear + 1] = -1;

			break;
		}
	}

}

DLL_EXPORT void identifier_decl(std::unordered_map<unsigned, std::string> && hashes) {
	//int n = getnameloc("ident", *ptable) + 1;

	//handledeclident({ (char*)GROUP_PTR_AND_SZ(n) });
	//adddeclarationident((char*)GROUP_PTR_AND_SZ(n), false);

	//currtypevectorbeingbuild.back().p->back().identifier = { FIRST_ARG_PTR_AND_SZ };//(char*)GROUP_PTR_AND_SZ(n) };

	var var;

	type basic{ type::BASIC };

	basic.spec.basicdeclspec.basic[3] = hashes["typedefnmmatched"_h];;

	//basic.spec.basicdeclspec.basic[0] = hashes["structorunionlast"_h];

	//basic.spec.basicdeclspec.basic[3] = hashes["identlasttag"_h];

	//if (basic.spec.basicdeclspec.basic[3].empty())

	var.identifier = hashes["ident_decl"_h];

	var.type = { basic };

	var.linkage = hashes["typedefkey"_h];

	/*basic.spec.basicdeclspec.basic[3] = hashes["typedefnmmatched"_h];



	if (const char* pidentraw = var.identifier.c_str())
	{
	}*/

	currtypevectorbeingbuild.back().p->push_back(var);
}

DLL_EXPORT void add_type(std::unordered_map<unsigned, std::string>&hashes) {
	auto& lastvar = currtypevectorbeingbuild.back().p->back();
	parsebasictypenspecs({ hashes["typefound"_h] }, lastvar);
}

DLL_EXPORT void add_qualif(std::unordered_map<unsigned, std::string>&hashes) {
	auto& lastvar = currtypevectorbeingbuild.back().p->back();
	//lastvar.linkage = hashes["storageclass"_h];
	parsebasictypenspecs({ hashes["qualiffound"_h] }, lastvar);
}

DLL_EXPORT void add_tag(std::unordered_map<unsigned, std::string>&hashes) {
	auto& lastvar = currtypevectorbeingbuild.back().p->back();
	lastvar.type.back().spec.basicdeclspec.basic[0] = hashes["structorunionlast"_h];
	lastvar.type.back().spec.basicdeclspec.basic[3] = hashes["lasttag"_h];
}

DLL_EXPORT void enddeclaration(std::unordered_map<unsigned, std::string>&hashes) {
	auto& lastvar = currtypevectorbeingbuild.back().p->back();

	std::rotate(lastvar.type.begin(), ++lastvar.type.begin(), lastvar.type.end());

	auto lasttype = lastvar.type;

	//lastvar.type.clear();

	//expandtype(lasttype, lastvar.type);

	//lastvar.firstintroduced = scopevar.size();

	//currtypevectorbeingbuild.pop_back();
}
//virtual void unused_50() { };
DLL_EXPORT void add_literal(std::unordered_map<unsigned, std::string> &hashes) {
	if (hashes["begincharliteral"_h] == "\"") {
		phndl->constructstring();
		currstring = "";
	}
	else {
		std::stringstream ssstream;
		ssstream << (int)currstring[0];
		insertinttoimm(ssstream.str().c_str(), ssstream.str().size(), "", 0, 3);
		currstring = "";
	}
}

DLL_EXPORT void struc_or_union_body(std::unordered_map<unsigned, std::string> &hashes) {
	//auto& lastvar = currtypevectorbeingbuild.back().p->back();

	var tmp;
	type typestruct{ type::BASIC };
	typestruct.spec.basicdeclspec.basic[3] = hashes["lasttag"_h];
	typestruct.spec.basicdeclspec.basic[0] = hashes["structorunionlast"_h];
	tmp.type.push_back(typestruct);
	tmp.identifier = hashes["lasttag"_h];
	structorunionmembers.back().push_back({ tmp });
	currtypevectorbeingbuild.push_back(
		{ --structorunionmembers.back().end(), currdecltypeenum::STRUCTORUNION });
}

const llvm::fltSemantics& getfltsemfromtype(::type flttype) {
	return flttype.spec.basicdeclspec.basic[1] == "double" ?
		flttype.spec.basicdeclspec.longspecsn == 1 ? llvm::APFloatBase::PPCDoubleDouble()
		: llvm::APFloatBase::IEEEdouble() :
		(assert(flttype.spec.basicdeclspec.basic[1] == "float"),
			llvm::APFloatBase::IEEEsingle());
}
DLL_EXPORT void collect_float_literal(std::unordered_map<unsigned, std::string> &hashes) {
	std::string wholepart, fractionpart, exponent, exponent_sign;
	std::string ntoclear;
	if ((ntoclear = hashes["wholeopt"_h]).empty())
		if ((ntoclear = hashes["whole"_h]).empty())
			if ((ntoclear = hashes["wholenodot"_h]).empty())
				goto rest;

	if (wholepart.empty())
		wholepart = ntoclear;
rest:
	ntoclear = hashes["fraction"_h];//getnameloc2("fraction", *ptable, a, 0);

	if (fractionpart.empty())
		fractionpart = ntoclear;

	ntoclear = hashes["signexp"_h];

	if (exponent_sign.empty())
		exponent_sign = ntoclear;

	ntoclear = hashes["exp"_h];

	if (exponent.empty())
		exponent = ntoclear;
	std::list<::type> currtype = { 1, ::type::BASIC };

	llvm::Type* pllvmtype;

	std::string postfix = hashes["suffixflt"_h];

	const llvm::fltSemantics& floatsem = postfix.empty() ? currtype.back().spec.basicdeclspec.basic[1] = "double",
		pllvmtype = llvm::Type::getDoubleTy((*llvmctx)),
		llvm::APFloatBase::IEEEdouble() : _Ranges::contains(std::array{ "f", "F" }, postfix) ? currtype.back().spec.basicdeclspec.basic[1] = "float",
		pllvmtype = llvm::Type::getFloatTy((*llvmctx)),
		llvm::APFloatBase::IEEEsingle() : (assert(_Ranges::contains(std::array{ "l", "L" }, postfix)),
		 currtype.back().spec.basicdeclspec.basic[1] = "double", currtype.back().spec.basicdeclspec.longspecsn = 1,
		  pllvmtype = llvm::Type::getPPC_FP128Ty((*llvmctx)), llvm::APFloatBase::PPCDoubleDouble());

	llvm::APFloat floatlit{ floatsem };

	std::string finalnumber = wholepart + "." + fractionpart;

	if (!exponent.empty())
		finalnumber += "E" + exponent_sign + exponent;

	if(hashes["nan"_h].empty()) {
		auto status = floatlit.convertFromString(finalnumber, llvm::APFloatBase::rmNearestTiesToEven);
		assert(status);
	}

	llvm::Constant *pconstant = llvm::ConstantFP::get(pllvmtype, hashes["nan"_h].empty() ? floatlit :  llvm::APFloat::getNaN(floatsem));

	immidiates.push_back({ currtype, pconstant });
}

DLL_EXPORT void end_binary() {
	phndl->end_binary();
}
DLL_EXPORT void begin_branch() {
	phndl->begin_branch();
}
DLL_EXPORT void begin_binary() {
	phndl->begin_binary();
}

DLL_EXPORT void add_ident_to_enum_def(std::unordered_map<unsigned, std::string> &hashes) {
	var tmp;
	type enumtype{ type::BASIC };
	enumtype = basicint;

	tmp.type.push_back(enumtype);

	//tmp.pllvmtype = buildllvmtypefull(tmp.type);

	//int n = getnameloc3("identlast", *ptable, a, 1, { .dontsearchforclosest = 0 }) + 1;

	tmp.identifier = hashes["identlasttag"_h];//(char*)GROUP_PTR_AND_SZ(n) };
	tmp.isconstant = true;

	scopevar.back().push_back(tmp);

	enums.back().back().memberconstants.push_back(--scopevar.back().end());
}
DLL_EXPORT void begin_enumerator_def(std::unordered_map<unsigned, std::string> && hashes) {
	//begin_enumerator_decl(pargs, szargs);
	enums.back().push_back({ hashes["lasttag"_h], {} });
	//add_tag(hashes);
}
/*DLL_EXPORT void begin_enumerator_decl(const char** pargs, size_t* szargs) {
	//int n = getnameloc3("identlast", *ptable, a, 1, { .dontsearchforclosest = 0 }) + 1;
	currenum = { FIRST_ARG_PTR_AND_SZ };
}*/
void announce_enum_def() {
	auto vartopush = enums.back().back().memberconstants.back();
	auto vartopushcopy = *vartopush;
	vartopushcopy.seralise();
	vartopushcopy.type.front().spec.basicdeclspec.basic[1] = "enum";
	vartopushcopy.type.front().spec.basicdeclspec.longspecsn = dyn_cast<llvm::ConstantInt>(vartopush->constant)->getSExtValue();
	auto idtostore = callstring("getidtostor", vartopush->identifier.c_str(), vartopush->identifier.length());
	assert(idtostore != -1);
	{
		std::unique_lock lck{ boradcastingscope };
		scopevars_global[stringhash(vartopush->identifier.c_str())][idtostore] = vartopushcopy;
	}
	callint("broadcastid", idtostore, vartopush->identifier.c_str(), vartopush->identifier.size());
}

DLL_EXPORT void end_ass_to_enum_def() {
	enums.back().back().memberconstants.back()->constant = immidiates.back().constant;
	enums.back().back().maxcount = dyn_cast<llvm::ConstantInt>(enums.back().back().memberconstants.back()->constant)->getSExtValue() + 1;
	immidiates.pop_back();
	endconstantexpr();
	announce_enum_def();
}
DLL_EXPORT void end_without_ass_to_enum_def() {
	enums.back().back().memberconstants.back()->constant = llvm::ConstantInt::get((*llvmctx), llvm::APInt(getInt32Ty(*llvmctx)->getBitWidth(), enums.back().back().maxcount++));
	announce_enum_def();
}

DLL_EXPORT void global_han(const char* fnname, std::unordered_map<unsigned, std::string> && hashes, void(*pfunc)(...)) {
	if (binabrupt) {
		if (std::string{ fnname } == "endfndef") {
			binabrupt = false;
		}
	}

	if (allowdebug && llvmbuilder && pfunc && llvmsub) {
		llvmbuilder->SetCurrentDebugLocation(llvm::DILocation::get(*llvmctx, evalperlexpruv("pos()"), 0, llvmsub));
	}
	else {
		llvmbuilder->SetCurrentDebugLocation({});
	}
}
#if 0
virtual void begin_unnamed_enum_def_94() {
	enums.back().push_back({ {}, {} });
}
virtual void end_expr_init_95() {
	auto val = immidiates.back();
	immidiates.pop_back();
	obtainvalbyidentifier(scopevar.back().back().identifier);
	immidiates.push_back(val);
	assigntwovalues();
	immidiates.pop_back();
}
virtual llvm::Value* assigntwovalues() = 0;

static std::list<val>& immidiates;

std::list<val>& bindings_compiling::immidiates = ::immidiates;

#endif


extern "C" {
#include <EXTERN.h> /* from the Perl distribution     */
#include <perl.h>	/* from the Perl distribution     */
#include <XSUB.h>
}
#undef wait
#undef write

DLL_EXPORT unsigned docall(const char*, size_t, void*);

void call(std::unordered_map<unsigned, std::string> hash, std::string callname) {
	//SvREFCNT_dec(hash);

	docall(callname.c_str(), callname.length(), &hash);

	//SvREFCNT_dec(hash);
}

std::queue<std::pair<std::unordered_map<unsigned, std::string>, std::string>> callstack;

extern "C" PerlInterpreter * my_perl;

extern "C" void* wait_for_call(void*) {
	do {
		std::unique_lock lock{ mutexwork };
		condwake.wait(lock, [] {return !callstack.empty() || endwork; });

		while (!callstack.empty()) {
			auto callinfo = callstack.front();
			callstack.pop();
			lock.unlock();
			call(callinfo.first, callinfo.second);
			lock.lock();
		}

	} while (!endwork);
	return nullptr;
}

static std::list<std::pair<std::unordered_map<unsigned, std::string>, std::string>> recordstack;

extern "C" THREAD_LOCAL_C unsigned int matchpos;


namespace callout_namespace {

	static THREAD_LOCAL char * pinstr;
	static THREAD_LOCAL std::unordered_map<unsigned, std::string> map;
}

DLL_EXPORT void handler1(int sig) {
	using namespace callout_namespace;
	printf("signal %d @ %lu\n", sig, evalperlexpruv("pos()"));
	printf("at callout %s\n", pinstr);
	for(auto &obj : map) {
		printf("[%s] ", obj.second.c_str());
	}
	printf("\n");
	//dumpabrupt();
	//exit(0);
	//raise(sig);
	/*if (!initial)
		call_argv("decnthreads", G_DISCARD | G_NOARGS, NULL);
	else {
		call_argv("waitforthreads", G_DISCARD | G_NOARGS, NULL);
	}*/
	//pthread_exit(NULL);
	/*if(areweinuser)
		siglongjmp(docalljmp, 1);
	else {
		printf("unhandled\n");
		//exit(-1);
		die("unhandled");
	}*/
#ifndef _WIN32
	exc_longjmp(docalljmp, 1);
#endif
}

DLL_EXPORT U32 do_callout(SV * in, HV * hash, U32 pos)
{
	using namespace callout_namespace;
	matchpos = pos;
	map.clear();

	char* key;
	I32 key_length;
	STRLEN inlen;
	SV* value;
	hv_iterinit(hash);
	const char nill[1] = { '\0' };
	while (value = hv_iternextsv(hash, &key, &key_length)) {
		pinstr = SvPVutf8(value, inlen);
		if (!inlen) continue;
		if (record.is_open() && recordstack.empty()) {
			record.write(pinstr, inlen);
			record.write(nill, 1);
			auto hash = stringhash(std::string{ key, (size_t)key_length }.c_str());
			record.write((char*)&hash, 4);
		}
		else {
			map.insert({ stringhash(std::string{key, (size_t)key_length}.c_str()), std::string{pinstr, inlen} });
		}
	}

	pinstr = SvPVutf8(in, inlen);

	if (!recordstack.empty()) {
		recordstack.push_back({ map, std::string{pinstr, inlen} });
	}
	else if (record.is_open()) {

		record.write(nill, 1);
		record.write(pinstr, inlen);
		record.write(nill, 1);
	}
	else {
		if (getenv("THREADING")) {
			mutexwork.lock();

			callstack.push({ map, std::string{pinstr, inlen} });

			mutexwork.unlock();

			condwake.notify_one();
		}
		else {
			return docall(pinstr, inlen, &map);
		}
	}

	return 0;
}


DLL_EXPORT void startrecording() {
	recordstack.push_back({});
}

DLL_EXPORT void stoprecording() {
	recordstack.pop_back();
}

extern "C" int secondmain(char* subject, size_t szsubject, char* pattern,
	size_t szpattern, char* modulename, size_t szmodulename,
	char* entrypoint, size_t szentrypoint) {

	std::string entry{ entrypoint, szentrypoint };

	auto iterentry = std::find_if(recordstack.begin(), recordstack.end(), [&](decltype(recordstack.back())& elem) {
		return elem.second == entry;
		});





	//startmodule(modulename, szmodulename);
	return 0;
}
