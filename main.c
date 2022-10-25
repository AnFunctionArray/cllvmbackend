#define PCRE2_CODE_UNIT_WIDTH 8
#define PCRE2_STATIC
#define _LARGEFILE64_SOURCE

#ifdef NDEBUG
#define NDEBUGSTATE
#endif
#include <setjmp.h>
extern __thread jmp_buf docalljmp;

#if !defined(_WIN32) & !defined(_WIN64)
//#include <pcre2.h>
#else
//#include <pcre2/pcre2.h>
#endif
#include <stdio.h>
//#include <boost/preprocessor/stringize.hpp>
#include <string.h>
#include <stdlib.h>
#include <stdarg.h>

#include "main.h"
//#include <oniguruma.h>

#if 0

FILE* foutput, *foutput2;

int callout_test(pcre2_callout_block* a, void* b);

static int bwasdebugprinted;

char* getnameloc3(long long int ntocompare, struct calloutinfo nametable, pcre2_callout_block* pcurrblock, int displ, struct namelocopts opts)
{
	PCRE2_SPTR tabptr = nametable.name_table;

	char* str = (char*)ntocompare;

	if (ntocompare > 0)
		printf2("%s: ", str);

	if (!bwasdebugprinted)
		printf("\n\n");

	uint32_t namecount = nametable.namecount, n, lastvalidn = -1, lastndist = UINT32_MAX;

	if (opts.rev)
		tabptr += (namecount - 1) * nametable.name_entry_size;

	for (; namecount--; !opts.rev ? tabptr += nametable.name_entry_size : (tabptr -= nametable.name_entry_size))
	{
		n = (tabptr[0] << 8) | tabptr[1];

		if (!bwasdebugprinted) printf2("%s - %d\n", tabptr + 2, n);

		if (ntocompare > 0 && !strcmp(tabptr + 2, str))
		{
			if (!pcurrblock)
				return printf2("\n"), n;

			if (opts.dontsearchforclosest, 1)
			{
				int isok = pcurrblock->offset_vector[2 * (n + displ)] != -1;

				if (opts.last)
					if (isok)
						lastvalidn = n;
					else;
				else
					lastvalidn = n;
				// && (!pcurrblock || (lastvalidn = n, pcurrblock->offset_vector[2 * (n + displ)] != -1))
				pcre2_callout_block* a = pcurrblock;
				if (!opts.last && isok)
					return printf2("%.*s \n", GROUP_SZ_AND_PTR(n + displ)), n;
			}
			else {
				long long dist = (long long)pcurrblock->capture_last - n;
				if (llabs(dist) <= llabs(lastndist))
					lastndist = dist,
					lastvalidn = n;
			}
		}
		else if (n == -ntocompare)
			return tabptr + 2;
	}

	if (!bwasdebugprinted)
		printf("\n\n");

	bwasdebugprinted = 1;

	pcre2_callout_block* a = pcurrblock;
	if (!(ntocompare > 0)) return "";
	else return lastvalidn != -1 ? printf2("%d %d %d %.*s \n", pcurrblock->capture_last, lastndist, lastvalidn, GROUP_SZ_AND_PTR(lastvalidn + displ)) : printf2("\n"), lastvalidn;
}

char* getnameloc2(long long int ntocompare, struct calloutinfo nametable, pcre2_callout_block* pcurrblock, int displ)
{
	return getnameloc3(ntocompare, nametable, pcurrblock, displ, (struct namelocopts) { .rev = 0, .last = 0, .dontsearchforclosest = 0, });
}

char* getnameloc(long long int ntocompare, struct calloutinfo nametable) {
	return getnameloc2(ntocompare, nametable, 0, 0);
}

int compile_pattern_and_execute(const char* pattern, const char* subject, int (*callback)(pcre2_callout_enumerate_block*, void*), size_t szpattern, size_t szsubject, int msgs, size_t* plen, int flags)
{
	int error, ncaptures, namecount, name_entry_size, n, rc;
	PCRE2_SIZE erroroffset, * povector;

	char* pstr;

	uint32_t ovectorcount;

	/*char* exprregex = "(\\b(\\w+)\\b)|(\\b(((0x)|(0b)|(0))(\\d+)|([0-9a-fA-F]))\\b)"
		"|(\\b\'(\\\\((x)|(b)|(0))(\\d+)|([0-9a-fA-F])|(\\')|(n)|(t))|(.)\'\\b)"
		"|(\\b\"(\\\\((x)|(b)|(0))(\\d+)|([0-9a-fA-F])|(\\\")|(n)|(t))|(.)\"\\b)";*/

	PCRE2_SPTR name_table, tabptr;

	pcre2_match_data* pmatch_data = pcre2_match_data_create(0xFFFF, 0);

	pcre2_match_context* match_context = pcre2_match_context_create(0);

	pcre2_code* pcode;

	PCRE2_UCHAR* pnewsubstr = pattern; //malloc(szpattern);

	PCRE2_SIZE newsubstrlen = szpattern;

	char errormsg[0xFF];

	struct calloutinfo nametable;

	//"\"(((\\\\((x)|(b)|(0))(\\d+)|([0-9a-fA-F]+)|(\\\")|(n)|(t))*(?C2))|((.*)(?C3)))*\"(?C1)"

	if (msgs, 0)
		printf("%.*s\n", szsubject, subject);
	//pcode = pcre2_compile("\\s|\\n", PCRE2_ZERO_TERMINATED, 0, &error, &erroroffset, 0);

	//pcre2_substitute(pcode, pattern, szpattern, 0, PCRE2_SUBSTITUTE_GLOBAL, pmatch_data, match_context, "", 0, pnewsubstr, &newsubstrlen);

	//pcre2_match_context_free(match_context), pcre2_match_data_free(pmatch_data);

	//pmatch_data = pcre2_match_data_create(0xFFFF, 0);

	//match_context = pcre2_match_context_create(0);

	if (msgs)
		printf("%.*s\n\n", (unsigned int)newsubstrlen, pnewsubstr);

	//free(pattern);

	pcode = pcre2_compile(pnewsubstr, newsubstrlen, flags, &error, &erroroffset, 0);

	int resjit = pcre2_jit_compile(pcode, PCRE2_JIT_COMPLETE);

	if (error != 100)
		pcre2_get_error_message(error, errormsg, 0xFF),
		printf("pattern error %d at %s : %.*s\n", error, errormsg, (unsigned int)(newsubstrlen - erroroffset), pnewsubstr + erroroffset);

	pcre2_pattern_info(pcode, PCRE2_INFO_NAMETABLE, &nametable.name_table);

	pcre2_pattern_info(pcode, PCRE2_INFO_NAMECOUNT, &nametable.namecount);

	pcre2_pattern_info(pcode, PCRE2_INFO_NAMEENTRYSIZE, &nametable.name_entry_size);

	nametable.pattern = pnewsubstr;
	nametable.szpattern = newsubstrlen;
	nametable.pmatchdata = pmatch_data;

	//static int dequeadd(val, pqueue, ptail, phead, empty, full, size)

	//dequeadd(nametable, nametablequeue, &ptail, &phead, &empty, &full, _countof(nametablequeue));

	pcre2_set_callout(match_context, callback, &nametable);

	if (msgs)
		printf("\n\n", 0);

	rc = pcre2_match(pcode, subject, szsubject, 0, MATCH_FLAGS, pmatch_data, match_context);

	printf("%d\n", rc);

	ovectorcount = pcre2_get_ovector_count(pmatch_data);

	povector = pcre2_get_ovector_pointer(pmatch_data);

	printf("full match is: %d - %d, %.*s\n", povector[0], povector[1], (unsigned int)(povector[1] - povector[0]),
		subject + povector[0]);

	if (plen)
		*plen = povector[1] - povector[0];

	pcre2_match_data_free(pmatch_data);

	pcre2_match_context_free(match_context);

	return rc;
}
char* openfile(char* chname, size_t* szfileout)
{
	FILE* fregex = fopen(chname, "rt");
	size_t szfile;
	char* filecontent;

	fseek(fregex, 0, SEEK_END);
	fgetpos(fregex, &szfile);

	filecontent = malloc(szfile + !szfileout);

	rewind(fregex);

	fread(filecontent, szfile, 1, fregex);

	fclose(fregex);

	while (--szfile && (filecontent[szfile] == '\xCD' || filecontent[szfile] == '\x9'))
		; //printf(" %x ", (unsigned char)filecontent[szfile]);

	if (szfileout)
		*szfileout = szfile + 1;
	else
		filecontent[szfile + 1] = '\0';

	return filecontent;
}

//#include "llvm/llvmgen.h"

secondmain(char* subject, size_t szsubject, char* pattern, size_t szpattern, char* modulename, size_t szmodulename)
{
	startmodule(modulename, szmodulename);
	int stat = compile_pattern_and_execute(pattern, subject, callout_test, szpattern, szsubject, 1, 0, PATTERN_FLAGS);
}

struct retgetnamevalue getnamevalue(const char* nametoget) {
	struct retgetnamevalue retgetnamevalue;
	SV* var = get_sv(nametoget, GV_ADD);   /* need "Foo::" now */
	retgetnamevalue.ptr = SvPVutf8(var, retgetnamevalue.sz);
	return retgetnamevalue;
}

#endif

#include <EXTERN.h> /* from the Perl distribution     */
#include <perl.h>	/* from the Perl distribution     */
#include <XSUB.h>

XS__startmatching(), XS__callout(), XS__startmodule(), boot_DynaLoader(), endmodule()
, XS__initthread1(), waitforthread(), preparethread(), XS__startmetaregex(), dumpabrupt(),
endmoduleabrupt(), dumpmodule(), XS__flushfilescopes1(), XS__consumefilescopes1(),
XS__registerthread1(), XS__broadcast1(), resetbufferthr(), XS__updateavailidents1();

static void
xs_init(pTHX)
{
	/* DynaLoader is a special case */
	newXS("DynaLoader::boot_DynaLoader", boot_DynaLoader, __FILE__);
	newXS("startmatching", XS__startmatching, __FILE__);
	newXS("callout", XS__callout, __FILE__);
	//newXS("startmetaregex", XS__startmetaregex, __FILE__);
	newXS("endmodule", endmodule, __FILE__);
	newXS("endmoduleabrupt", endmoduleabrupt, __FILE__);
	newXS("initthread", XS__initthread1, __FILE__);
	newXS("dumpmodule", dumpmodule, __FILE__);
	//newXS("preparethread", preparethread, __FILE__);
	newXS("waitforthread", waitforthread, __FILE__);
	newXS("startmodule", XS__startmodule, __FILE__);
	newXS("flushfilescopes", XS__flushfilescopes1, __FILE__);
	newXS("consumefilescopes", XS__consumefilescopes1, __FILE__);
	newXS("registerthread", XS__registerthread1, __FILE__);
	newXS("broadcast", XS__broadcast1, __FILE__);
	//newXS("resetbuffer", resetbufferthr, __FILE__);
	newXS("updateavailidents", XS__updateavailidents1, __FILE__);
}

PerlInterpreter* my_perl; /***    The Perl interpreter    ***/
//pthread_t thread;
#if 0
#include <userenv.h>
#include <wtsapi32.h>
#endif
#if 0
int callout(OnigCalloutArgs* args, void* user_data) {
	const char *pfuncname = onig_get_contents_by_callout_args(args);
	return f();
}

secondmain(char* subject, size_t szsubject, char* pattern, size_t szpattern, char* modulename, size_t szmodulename)
{
	startmodule(modulename, szmodulename);
	//int stat = compile_pattern_and_execute(pattern, subject, callout_test, szpattern, szsubject, 1, 0, PATTERN_FLAGS);
	regex_t *preg;
	OnigErrorInfo err_info;
	onig_new(&preg, pattern, pattern + szpattern,
	 ONIG_OPTION_MULTILINE | ONIG_OPTION_EXTEND, ONIG_ENCODING_UTF8, ONIG_SYNTAX_DEFAULT, &err_info);

	onig_search(preg, subject, subject + szsubject, subject, subject + szsubject, 0, 0);
}
#endif
#include <pthread.h>
#include <signal.h>
//#include <unistd.h>

__thread U32 matchpos, basepos;

__thread int initial;

__thread int areweinuser;

unsigned int evalperlexpruv(const char *what) {
	SV *currpos = eval_pv(what, FALSE);
	unsigned long pos =  SvUV(currpos);
	//sv_free(currpos);
	return pos;
}

void handler1(int sig) {
	printf("signal %d @ %lu\n", sig, evalperlexpruv("pos()"));
	//dumpabrupt();
	//exit(0);
	raise(sig);
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

	siglongjmp(docalljmp, 1);
}

int
getidentid(what, sizewhat)
const char *what;
size_t sizewhat;
{
    dSP;

    ENTER;
    SAVETMPS;

	unsigned long res = 0;

    PUSHMARK(SP);
    EXTEND(SP, 1);
    PUSHs(sv_2mortal(newSVpvn(what, sizewhat)));
    PUTBACK;

    res = call_pv("getidentid", G_SCALAR);

    SPAGAIN;

	res = POPu;

    PUTBACK;
    FREETMPS;
    LEAVE;

	return res;
}

#ifdef _WIN32
#include 	<crtdbg.h>
#endif

int handler2(int reportType, char* message, int* returnValue) {
	if (returnValue)
		*returnValue = TRUE;
	printf("%s\n", message);
	dumpabrupt();
	exit(0);
}
#ifdef _WIN32
WINBASEAPI
_Ret_maybenull_
PVOID
WINAPI
AddVectoredExceptionHandler(
	_In_ ULONG First,
	_In_ PVECTORED_EXCEPTION_HANDLER Handler
);

LONG WINAPI
VectoredHandler1(
	struct _EXCEPTION_POINTERS* ExceptionInfo
)
{
	dumpabrupt();

	return EXCEPTION_EXECUTE_HANDLER;
}
#endif
int main(int argc, char** argv, char** env)
{
	initial = 1;
	//onig_initialize((OnigEncoding[]){&OnigEncodingUTF8}, 1);
#if 0
	//argv[0] = "D:\\perl5\\perl.exe";
	//env = (char* []){ "PATH=D:\\perl5", 0 };
	LPVOID lpenv;
	HANDLE htoken;
	//WTSQueryUserToken(0, &htoken);
	OpenProcessToken(GetCurrentProcess(), TOKEN_READ, &htoken);
	CreateEnvironmentBlock(&lpenv, htoken, false);
	const char* env[0xFF] = { GetEnvironmentStrings() }, ** pcurr = env;
	const char* tmp;
	for (const wchar_t* curr = lpenv; *curr; curr += wcslen(curr) + 1)
		wcstombs(tmp = malloc(0xFFF), curr, 0xFFF), *pcurr++ = tmp;
#endif
	//onig_initialize();
	signal(SIGTERM, handler1);
	signal(SIGABRT, handler1);
	signal(SIGSEGV, handler1);
#if _WIN32 && defined(NDEBUGSTATE)
	_CrtSetReportHook(handler2);
	AddVectoredExceptionHandler(1, VectoredHandler1);
#endif
	if(getenv("THREADING")) {
		void *wait_for_call(void*);
		//pthread_create(&thread, 0, wait_for_call, 0);
	}
	PERL_SYS_INIT3(&argc, &argv, &env);
	my_perl = perl_alloc();
	perl_construct(my_perl);
	PL_exit_flags |= PERL_EXIT_DESTRUCT_END;
	perl_parse(my_perl, xs_init, argc, argv, NULL);
	//foutput = fopen("output.txt", "wt");
	//foutput2 = fopen("output2.txt", "wt");
	llvminit();
	perl_run(my_perl);
	//fflush(foutput);
	//fflush(foutput2);

	//endmodule(0);
	//kill(0, 1);
	//exit(EXIT_SUCCESS);
	//endmodule();
	//dumpmodule();
	//endmodule();
	perl_destruct(my_perl);
	perl_free(my_perl);
	PERL_SYS_TERM();
}

#ifdef _WIN32

HANDLE hCurrModule;

void docall(const char *name, size_t szname, void *phashmap) {
	char cProcName[USHRT_MAX];
	sprintf(cProcName, "%.*s", szname, name);
	if (!hCurrModule) hCurrModule = GetModuleHandle(0);

	FARPROC pfunc = GetProcAddress(hCurrModule, cProcName);

	if (!pfunc) return;

	extern void global_han();

	global_han(cProcName, phashmap);

	//EXCEPTION_POINTERS* pexc;

	//__try {

		((void (*)(void* phashmap))pfunc)(phashmap);
	//}
	//__except (pexc=GetExceptionInformation(), EXCEPTION_EXECUTE_HANDLER) {
	//	__debugbreak();
	//}
}
#else
#include <dlfcn.h>
#include <setjmp.h>
__thread jmp_buf docalljmp;
__thread bool binabrupt;
U32 docall(const char *name, size_t szname, void *phashmap) {
	char cProcName[USHRT_MAX];
	sprintf(cProcName, "%.*s", (int)szname, name);
	//if (!hCurrModule) hCurrModule = GetModuleHandle(0);

	void *dlhndl = dlopen(0, RTLD_LAZY);

	//FARPROC pfunc = GetProcAddress(hCurrModule, cProcName);

	void *pfunc = dlsym(dlhndl, cProcName);

	extern void global_han();

	global_han(cProcName, phashmap);

	if (!pfunc) return 0;
	areweinuser = 1;
	if (!sigsetjmp(docalljmp, 1) && !binabrupt) {
		//printf("@thread %p\n", &matchpos);
		((void (*)(void* phashmap))pfunc)(phashmap);
		areweinuser = 0;
		return 0;
	}
	areweinuser = 0;
	return 1;
}

#endif

#if 0
main()
{
	size_t szfilepattern, szsubject;

	foutput = fopen("output.txt", "wt");

	char* pfilepattern = openfile(TEST_REGEX_FILE, &szfilepattern), * pfilesubject = openfile(TEST_FILE, &szsubject);
#ifndef TEST
	char* res = glueregexfile(TEST_REGEX_FILE);

	int stat = compile_pattern_and_execute(res, pfilesubject, callout_test, strlen(res), szsubject, 1, 0, PATTERN_FLAGS);
#else
	int stat = compile_pattern_and_execute(pfilepattern, pfilesubject, callout_test, szfilepattern, szsubject, 1, 0, PATTERN_FLAGS);
#endif

	fclose(foutput);

#if 0
	ovectorcount = pcre2_get_ovector_count(pmatch_data);

	povector = pcre2_get_ovector_pointer(pmatch_data);

	for (n = 0; n < rc; ++n)
		printf(
			"%d - %.*s\n",
			n,
			(unsigned int)(povector[2 * n + 1] - povector[2 * n]),
			subject + povector[2 * n]
		);
#endif
}
#endif

/*
* pcre2_pattern_info(pcode, PCRE2_INFO_NAMETABLE, &name_table);

	pcre2_pattern_info(pcode, PCRE2_INFO_NAMECOUNT, &namecount);

	pcre2_pattern_info(pcode, PCRE2_INFO_NAMEENTRYSIZE, &name_entry_size);

	tabptr = name_table;

	for (;namecount--; tabptr += name_entry_size)
	{
		n = (tabptr[0] << 8) | tabptr[1];

		printf("(%d) %*s: %.*s\n", (tabptr[0] << 8) | tabptr[1], name_entry_size - 3, tabptr + 2,
			(unsigned int)(povector[2 * n + 1] - povector[2 * n]), subject + povector[2 * n]);
	}
*/

/*static int dequeadd(val, pqueue, ptail, phead, empty, full, size)
int **empty, **full;
struct nametable* pqueue, **ptail, **phead, val;
{
	if (*full) return -1;

	**ptail = val;

	if ((*ptail - pqueue) + 1 == size)
		*ptail = pqueue;
	else ++*ptail;

	if (*ptail == *phead) *full = 1;

	return 0;
}

static int dequeremove(val, pqueue, ptail, phead, empty, full, size)
int ** empty, ** full;
struct nametable* pqueue, ** ptail, ** phead, *val;
{
	if (*empty) return -1;

	if (val) *val = **phead;

	if ((*phead - pqueue) + 1 == size)
		*phead = pqueue;
	else ++* phead;

	if (*ptail == *phead) *empty = 1;

	return 0;
}

static struct nametable nametablequeue[0xFF], *ptail = nametablequeue, *phead = nametablequeue;

static int full = 0, empty = 1;*/