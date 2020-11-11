// Lean compiler output
// Module: Lean.Meta.Tactic.Subst
// Imports: Init Lean.Meta.AppBuilder Lean.Meta.MatchUtil Lean.Meta.Tactic.Util Lean.Meta.Tactic.Revert Lean.Meta.Tactic.Intro Lean.Meta.Tactic.Clear Lean.Meta.Tactic.FVarSubst
#include <lean/lean.h>
#if defined(__clang__)
#pragma clang diagnostic ignored "-Wunused-parameter"
#pragma clang diagnostic ignored "-Wunused-label"
#elif defined(__GNUC__) && !defined(__CLANG__)
#pragma GCC diagnostic ignored "-Wunused-parameter"
#pragma GCC diagnostic ignored "-Wunused-label"
#pragma GCC diagnostic ignored "-Wunused-but-set-variable"
#endif
#ifdef __cplusplus
extern "C" {
#endif
lean_object* l_Lean_Meta_substCore___lambda__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withLocalDecl___at_Lean_Meta_substCore___spec__4(lean_object*);
size_t l_USize_add(size_t, size_t);
extern lean_object* l_Lean_Name_getString_x21___closed__3;
lean_object* l_Lean_Meta_substCore___lambda__3___boxed(lean_object**);
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_Meta_substCore___lambda__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkEqImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_subst___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_foldM_loop___at_Lean_Meta_substCore___spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_LocalDecl_isAuxDecl(lean_object*);
lean_object* lean_name_mk_string(lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_Lean_Meta_subst_match__1(lean_object*);
lean_object* l_Lean_Meta_substCore___lambda__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_subst___lambda__1___closed__4;
lean_object* l_Lean_Meta_substCore___lambda__7___boxed(lean_object**);
lean_object* l_Lean_Meta_substCore_match__6(lean_object*);
lean_object* l_Lean_Meta_substCore___lambda__13___closed__11;
lean_object* l_Std_PersistentArray_findSomeM_x3f___at_Lean_Meta_subst___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_subst___lambda__1___closed__2;
lean_object* l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Meta_isLevelDefEqAux___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp___rarg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_substCore___lambda__13___closed__26;
lean_object* l_Lean_Meta_substCore___lambda__13___closed__12;
lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkEqSymmImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
lean_object* l_Lean_Meta_substCore___lambda__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_substCore___lambda__2___boxed(lean_object**);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Meta_substCore___lambda__12___closed__1;
lean_object* l_Std_PersistentArray_findSomeMAux___at_Lean_Meta_subst___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_subst(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Lean_Meta_substCore___lambda__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_substCore_match__4___rarg(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofList(lean_object*);
lean_object* l_Lean_Meta_subst_match__2(lean_object*);
lean_object* l_Lean_Meta_substCore___lambda__8(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_substCore_match__2___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_subst___spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkEqReflImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalContext_findDeclM_x3f___at_Lean_Meta_subst___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_substCore___lambda__12___closed__2;
lean_object* l_Lean_Meta_substCore___lambda__13___closed__9;
uint8_t l_USize_decLt(size_t, size_t);
lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_subst___spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Meta_subst_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_substCore___lambda__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_subst_match__2___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_substCore___lambda__13___closed__3;
lean_object* l_Lean_LocalContext_findDeclM_x3f___at_Lean_Meta_subst___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withLocalDecl___at_Lean_Meta_substCore___spec__4___rarg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_substCore___lambda__13___closed__20;
lean_object* l_Lean_Meta_substCore___lambda__13___closed__10;
lean_object* l_Lean_Meta_substCore(lean_object*, lean_object*, uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_foldM_loop___at_Lean_Meta_substCore___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_addTrace___at_Lean_Meta_isLevelDefEqAux___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_replaceFVar(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_substCore___lambda__13___closed__16;
lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_subst___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
lean_object* l_Lean_Meta_subst_match__3___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_clear(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_substCore_match__3(lean_object*);
lean_object* l_Std_PersistentArray_findSomeMAux___at_Lean_Meta_subst___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_substCore___lambda__1(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars___at_Lean_Meta_SynthInstance_tryResolveCore___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_whnf___at___private_Lean_Meta_Basic_0__Lean_Meta_isClassExpensive_x3f___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_subst___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkEqNDRecImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkEqRecImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_revert(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withMVarContext___at_Lean_Meta_admit___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_substCore___lambda__10___boxed(lean_object**);
lean_object* l_Lean_Meta_getMVarDecl___at_Lean_Meta_isReadOnlyExprMVar___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_substCore___lambda__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_substCore___lambda__13___closed__21;
lean_object* l_Lean_Meta_substCore___lambda__13___closed__23;
lean_object* l_Lean_Meta_getLocalDecl___at_Lean_Meta_getFVarLocalDecl___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Util_0__mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_substCore___lambda__13___closed__13;
lean_object* l_Lean_Meta_introNCore(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_throwUnknownConstant___rarg___closed__3;
lean_object* l_Lean_Meta_substCore___lambda__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_substCore___lambda__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_subst_match__3(lean_object*);
extern lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Util___hyg_225____closed__1;
lean_object* l_Lean_Meta_substCore___lambda__13___closed__1;
lean_object* l_Lean_mkFVar(lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* l_Lean_Meta_substCore___lambda__6___boxed(lean_object**);
lean_object* l_Lean_Meta_substCore___lambda__13___closed__22;
lean_object* l_Lean_LocalDecl_fvarId(lean_object*);
lean_object* l_Lean_Meta_matchEq_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_substCore___lambda__13___closed__5;
lean_object* l_Lean_Meta_substCore___lambda__13___closed__14;
lean_object* l_Lean_LocalDecl_type(lean_object*);
lean_object* l_Nat_foldM_loop___at_Lean_Meta_substCore___spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MetavarContext_exprDependsOn(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_throwTacticEx___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEqNDRec___at_Lean_Meta_substCore___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_substCore___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Syntax_mkApp___closed__1;
lean_object* l_Lean_Meta_substCore___lambda__13___closed__25;
lean_object* l_Lean_Meta_subst___lambda__1___closed__3;
lean_object* l_Lean_Meta_substCore_match__5(lean_object*);
lean_object* l_Lean_Meta_substCore___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_foldM_loop___at_Lean_Meta_substCore___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getLocalDecl___at_Lean_Meta_getFVarLocalDecl___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Array_foldlMUnsafe_fold___at_Lean_withNestedTraces___spec__5___closed__1;
lean_object* l_Lean_Meta_checkNotAssigned(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEqRec___at_Lean_Meta_substCore___spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_substCore___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Init_Prelude___instance__67;
lean_object* l_Nat_foldM_loop___at_Lean_Meta_substCore___spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_foldM_loop___at_Lean_Meta_substCore___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_FVarSubst_insert(lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
lean_object* l_Lean_Meta_substCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_substCore___lambda__13___closed__7;
lean_object* l_Lean_Meta_subst___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_substCore___lambda__11___boxed(lean_object**);
lean_object* l_Lean_Meta_substCore___lambda__13___closed__18;
lean_object* l_Lean_Meta_substCore___lambda__13___closed__24;
lean_object* l_List_map___at_Lean_Meta_substCore___spec__8(lean_object*);
lean_object* l_Lean_Meta_substCore_match__6___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_substCore___lambda__9___boxed(lean_object**);
lean_object* l_Lean_Meta_substCore___lambda__13___closed__15;
lean_object* l_Lean_Meta_substCore___lambda__13___closed__19;
lean_object* l_Lean_Meta_substCore_match__1(lean_object*);
uint8_t l_Lean_Expr_isFVar(lean_object*);
lean_object* l_Lean_Meta_substCore_match__1___rarg(lean_object*, lean_object*);
lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_subst___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withMVarContext___at_Lean_Meta_revert___spec__5___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_substCore___lambda__11___closed__1;
lean_object* l_Lean_Meta_substCore___lambda__11___closed__4;
lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Subst___hyg_1143_(lean_object*);
lean_object* l_Lean_Meta_substCore___lambda__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_toList___rarg(lean_object*);
lean_object* l_Lean_Meta_substCore___lambda__11___closed__2;
lean_object* l_Lean_Meta_substCore___lambda__13(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_substCore___lambda__13___closed__2;
lean_object* l_Lean_Meta_substCore_match__4(lean_object*);
extern lean_object* l_Lean_Meta_throwLetTypeMismatchMessage___rarg___closed__1;
lean_object* l_Std_PersistentArray_findSomeM_x3f___at_Lean_Meta_subst___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withLocalDecl___at_Lean_Meta_substCore___spec__4___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_mkOptionalNode___closed__2;
lean_object* l_Lean_Meta_substCore___lambda__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_substCore___lambda__13___closed__4;
lean_object* l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_substCore___lambda__13___closed__17;
lean_object* l_Lean_Meta_substCore___lambda__13___closed__8;
lean_object* l_Lean_Meta_substCore_match__2(lean_object*);
lean_object* l_Lean_Meta_subst___lambda__1___closed__1;
lean_object* l_Lean_Meta_substCore_match__3___rarg(lean_object*, lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* l_Lean_Meta_getMVarTag___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEqSymm___at_Lean_Meta_substCore___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_substCore_match__5___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_substCore___lambda__5(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_substCore___lambda__11___closed__5;
lean_object* l_Lean_Meta_assignExprMVar___at___private_Lean_Meta_InferType_0__Lean_Meta_getLevelImp___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_substCore___lambda__13___closed__6;
extern lean_object* l_Array_findSomeM_x3f___rarg___closed__1;
lean_object* l_ReaderT_bind___at_Lean_Meta_Lean_Meta_Basic___instance__8___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_substCore___lambda__12(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_substCore___lambda__11___closed__3;
lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_subst___spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_substCore_match__1___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_apply_2(x_2, x_3, x_4);
return x_5;
}
}
lean_object* l_Lean_Meta_substCore_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_substCore_match__1___rarg), 2, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_substCore_match__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_3);
x_4 = lean_box(0);
x_5 = lean_apply_1(x_2, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
lean_dec(x_2);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_ctor_get(x_6, 1);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 0);
lean_inc(x_8);
lean_dec(x_6);
x_9 = lean_ctor_get(x_7, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_7, 1);
lean_inc(x_10);
lean_dec(x_7);
x_11 = lean_apply_3(x_3, x_8, x_9, x_10);
return x_11;
}
}
}
lean_object* l_Lean_Meta_substCore_match__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_substCore_match__2___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_substCore_match__3___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_apply_2(x_2, x_3, x_4);
return x_5;
}
}
lean_object* l_Lean_Meta_substCore_match__3(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_substCore_match__3___rarg), 2, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_substCore_match__4___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_apply_2(x_2, x_3, x_4);
return x_5;
}
}
lean_object* l_Lean_Meta_substCore_match__4(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_substCore_match__4___rarg), 2, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_substCore_match__5___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 1)
{
lean_object* x_4; uint64_t x_5; lean_object* x_6; lean_object* x_7; 
lean_dec(x_3);
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get_uint64(x_1, sizeof(void*)*1);
lean_dec(x_1);
x_6 = lean_box_uint64(x_5);
x_7 = lean_apply_2(x_2, x_4, x_6);
return x_7;
}
else
{
lean_object* x_8; 
lean_dec(x_2);
x_8 = lean_apply_1(x_3, x_1);
return x_8;
}
}
}
lean_object* l_Lean_Meta_substCore_match__5(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_substCore_match__5___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_substCore_match__6___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_3);
x_4 = lean_box(0);
x_5 = lean_apply_1(x_2, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
lean_dec(x_2);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_ctor_get(x_6, 1);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 0);
lean_inc(x_8);
lean_dec(x_6);
x_9 = lean_ctor_get(x_7, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_7, 1);
lean_inc(x_10);
lean_dec(x_7);
x_11 = lean_apply_3(x_3, x_8, x_9, x_10);
return x_11;
}
}
}
lean_object* l_Lean_Meta_substCore_match__6(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_substCore_match__6___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Nat_foldM_loop___at_Lean_Meta_substCore___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_unsigned_to_nat(0u);
x_12 = lean_nat_dec_eq(x_4, x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_nat_sub(x_4, x_13);
lean_dec(x_4);
x_15 = lean_nat_sub(x_3, x_14);
x_16 = lean_nat_sub(x_15, x_13);
lean_dec(x_15);
x_17 = lean_unsigned_to_nat(2u);
x_18 = lean_nat_add(x_16, x_17);
x_19 = l_Lean_Init_Prelude___instance__67;
x_20 = lean_array_get(x_19, x_1, x_18);
lean_dec(x_18);
x_21 = lean_array_get(x_19, x_2, x_16);
lean_dec(x_16);
x_22 = l_Lean_mkFVar(x_21);
x_23 = l_Lean_Meta_FVarSubst_insert(x_5, x_20, x_22);
x_4 = x_14;
x_5 = x_23;
goto _start;
}
else
{
lean_object* x_25; 
lean_dec(x_4);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_5);
lean_ctor_set(x_25, 1, x_10);
return x_25;
}
}
}
lean_object* l_Lean_Meta_mkEqNDRec___at_Lean_Meta_substCore___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkEqNDRecImp(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_9;
}
}
lean_object* l_Lean_Meta_mkEqSymm___at_Lean_Meta_substCore___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkEqSymmImp(x_1, x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
lean_object* l_Lean_Meta_withLocalDecl___at_Lean_Meta_substCore___spec__4___rarg(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
return x_10;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = lean_ctor_get(x_10, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_10);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
return x_14;
}
}
else
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_10);
if (x_15 == 0)
{
return x_10;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_10, 0);
x_17 = lean_ctor_get(x_10, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_10);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
}
}
lean_object* l_Lean_Meta_withLocalDecl___at_Lean_Meta_substCore___spec__4(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at_Lean_Meta_substCore___spec__4___rarg___boxed), 9, 0);
return x_2;
}
}
lean_object* l_Nat_foldM_loop___at_Lean_Meta_substCore___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_unsigned_to_nat(0u);
x_12 = lean_nat_dec_eq(x_4, x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_nat_sub(x_4, x_13);
lean_dec(x_4);
x_15 = lean_nat_sub(x_3, x_14);
x_16 = lean_nat_sub(x_15, x_13);
lean_dec(x_15);
x_17 = lean_unsigned_to_nat(2u);
x_18 = lean_nat_add(x_16, x_17);
x_19 = l_Lean_Init_Prelude___instance__67;
x_20 = lean_array_get(x_19, x_1, x_18);
lean_dec(x_18);
x_21 = lean_array_get(x_19, x_2, x_16);
lean_dec(x_16);
x_22 = l_Lean_mkFVar(x_21);
x_23 = l_Lean_Meta_FVarSubst_insert(x_5, x_20, x_22);
x_4 = x_14;
x_5 = x_23;
goto _start;
}
else
{
lean_object* x_25; 
lean_dec(x_4);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_5);
lean_ctor_set(x_25, 1, x_10);
return x_25;
}
}
}
lean_object* l_Lean_Meta_mkEqRec___at_Lean_Meta_substCore___spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkEqRecImp(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_9;
}
}
lean_object* l_Nat_foldM_loop___at_Lean_Meta_substCore___spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_unsigned_to_nat(0u);
x_12 = lean_nat_dec_eq(x_4, x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_nat_sub(x_4, x_13);
lean_dec(x_4);
x_15 = lean_nat_sub(x_3, x_14);
x_16 = lean_nat_sub(x_15, x_13);
lean_dec(x_15);
x_17 = lean_unsigned_to_nat(2u);
x_18 = lean_nat_add(x_16, x_17);
x_19 = l_Lean_Init_Prelude___instance__67;
x_20 = lean_array_get(x_19, x_1, x_18);
lean_dec(x_18);
x_21 = lean_array_get(x_19, x_2, x_16);
lean_dec(x_16);
x_22 = l_Lean_mkFVar(x_21);
x_23 = l_Lean_Meta_FVarSubst_insert(x_5, x_20, x_22);
x_4 = x_14;
x_5 = x_23;
goto _start;
}
else
{
lean_object* x_25; 
lean_dec(x_4);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_5);
lean_ctor_set(x_25, 1, x_10);
return x_25;
}
}
}
lean_object* l_List_map___at_Lean_Meta_substCore___spec__8(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; 
x_2 = lean_box(0);
return x_2;
}
else
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
x_6 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_6, 0, x_4);
x_7 = l_List_map___at_Lean_Meta_substCore___spec__8(x_5);
lean_ctor_set(x_1, 1, x_7);
lean_ctor_set(x_1, 0, x_6);
return x_1;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = lean_ctor_get(x_1, 0);
x_9 = lean_ctor_get(x_1, 1);
lean_inc(x_9);
lean_inc(x_8);
lean_dec(x_1);
x_10 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_10, 0, x_8);
x_11 = l_List_map___at_Lean_Meta_substCore___spec__8(x_9);
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
return x_12;
}
}
}
}
lean_object* l_Lean_Meta_substCore___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; 
x_16 = lean_array_get_size(x_1);
x_17 = lean_unsigned_to_nat(2u);
x_18 = lean_nat_sub(x_16, x_17);
lean_dec(x_16);
x_19 = 1;
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
x_20 = l_Lean_Meta_introNCore(x_10, x_18, x_2, x_19, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = !lean_is_exclusive(x_21);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_21, 0);
x_25 = lean_array_get_size(x_24);
lean_inc(x_25);
x_26 = l_Nat_foldM_loop___at_Lean_Meta_substCore___spec__1(x_1, x_24, x_25, x_25, x_3, x_11, x_12, x_13, x_14, x_22);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_25);
lean_dec(x_24);
if (x_4 == 0)
{
uint8_t x_27; 
lean_dec(x_9);
x_27 = !lean_is_exclusive(x_26);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_26, 0);
x_29 = l_Lean_Meta_FVarSubst_insert(x_28, x_5, x_6);
x_30 = l_Lean_Meta_FVarSubst_insert(x_29, x_7, x_8);
lean_ctor_set(x_21, 0, x_30);
lean_ctor_set(x_26, 0, x_21);
return x_26;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_31 = lean_ctor_get(x_26, 0);
x_32 = lean_ctor_get(x_26, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_26);
x_33 = l_Lean_Meta_FVarSubst_insert(x_31, x_5, x_6);
x_34 = l_Lean_Meta_FVarSubst_insert(x_33, x_7, x_8);
lean_ctor_set(x_21, 0, x_34);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_21);
lean_ctor_set(x_35, 1, x_32);
return x_35;
}
}
else
{
uint8_t x_36; 
lean_dec(x_6);
x_36 = !lean_is_exclusive(x_26);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_26, 0);
x_38 = l_Lean_Meta_FVarSubst_insert(x_37, x_5, x_9);
x_39 = l_Lean_Meta_FVarSubst_insert(x_38, x_7, x_8);
lean_ctor_set(x_21, 0, x_39);
lean_ctor_set(x_26, 0, x_21);
return x_26;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_40 = lean_ctor_get(x_26, 0);
x_41 = lean_ctor_get(x_26, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_26);
x_42 = l_Lean_Meta_FVarSubst_insert(x_40, x_5, x_9);
x_43 = l_Lean_Meta_FVarSubst_insert(x_42, x_7, x_8);
lean_ctor_set(x_21, 0, x_43);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_21);
lean_ctor_set(x_44, 1, x_41);
return x_44;
}
}
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_45 = lean_ctor_get(x_21, 0);
x_46 = lean_ctor_get(x_21, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_21);
x_47 = lean_array_get_size(x_45);
lean_inc(x_47);
x_48 = l_Nat_foldM_loop___at_Lean_Meta_substCore___spec__1(x_1, x_45, x_47, x_47, x_3, x_11, x_12, x_13, x_14, x_22);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_47);
lean_dec(x_45);
if (x_4 == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
lean_dec(x_9);
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_48, 1);
lean_inc(x_50);
if (lean_is_exclusive(x_48)) {
 lean_ctor_release(x_48, 0);
 lean_ctor_release(x_48, 1);
 x_51 = x_48;
} else {
 lean_dec_ref(x_48);
 x_51 = lean_box(0);
}
x_52 = l_Lean_Meta_FVarSubst_insert(x_49, x_5, x_6);
x_53 = l_Lean_Meta_FVarSubst_insert(x_52, x_7, x_8);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_46);
if (lean_is_scalar(x_51)) {
 x_55 = lean_alloc_ctor(0, 2, 0);
} else {
 x_55 = x_51;
}
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_50);
return x_55;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
lean_dec(x_6);
x_56 = lean_ctor_get(x_48, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_48, 1);
lean_inc(x_57);
if (lean_is_exclusive(x_48)) {
 lean_ctor_release(x_48, 0);
 lean_ctor_release(x_48, 1);
 x_58 = x_48;
} else {
 lean_dec_ref(x_48);
 x_58 = lean_box(0);
}
x_59 = l_Lean_Meta_FVarSubst_insert(x_56, x_5, x_9);
x_60 = l_Lean_Meta_FVarSubst_insert(x_59, x_7, x_8);
x_61 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_46);
if (lean_is_scalar(x_58)) {
 x_62 = lean_alloc_ctor(0, 2, 0);
} else {
 x_62 = x_58;
}
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_57);
return x_62;
}
}
}
else
{
uint8_t x_63; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_63 = !lean_is_exclusive(x_20);
if (x_63 == 0)
{
return x_20;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_64 = lean_ctor_get(x_20, 0);
x_65 = lean_ctor_get(x_20, 1);
lean_inc(x_65);
lean_inc(x_64);
lean_dec(x_20);
x_66 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_66, 0, x_64);
lean_ctor_set(x_66, 1, x_65);
return x_66;
}
}
}
}
lean_object* l_Lean_Meta_substCore___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18, lean_object* x_19) {
_start:
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = l_Lean_Meta_assignExprMVar___at___private_Lean_Meta_InferType_0__Lean_Meta_getLevelImp___spec__3(x_1, x_14, x_15, x_16, x_17, x_18, x_19);
x_21 = lean_ctor_get(x_20, 1);
lean_inc(x_21);
lean_dec(x_20);
x_22 = l_Lean_Expr_mvarId_x21(x_2);
if (x_6 == 0)
{
lean_object* x_23; 
lean_dec(x_13);
lean_dec(x_12);
x_23 = l_Lean_Meta_substCore___lambda__1(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_22, x_15, x_16, x_17, x_18, x_21);
return x_23;
}
else
{
lean_object* x_24; 
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
x_24 = l_Lean_Meta_clear(x_22, x_12, x_15, x_16, x_17, x_18, x_21);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
x_27 = l_Lean_Meta_clear(x_25, x_13, x_15, x_16, x_17, x_18, x_26);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
x_30 = l_Lean_Meta_substCore___lambda__1(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_28, x_15, x_16, x_17, x_18, x_29);
return x_30;
}
else
{
uint8_t x_31; 
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
x_31 = !lean_is_exclusive(x_27);
if (x_31 == 0)
{
return x_27;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_27, 0);
x_33 = lean_ctor_get(x_27, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_27);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
}
else
{
uint8_t x_35; 
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
x_35 = !lean_is_exclusive(x_24);
if (x_35 == 0)
{
return x_24;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_24, 0);
x_37 = lean_ctor_get(x_24, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_24);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
}
}
}
lean_object* l_Lean_Meta_substCore___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, uint8_t x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18, lean_object* x_19, lean_object* x_20, lean_object* x_21) {
_start:
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
lean_inc(x_17);
x_22 = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(x_1, x_2, x_17, x_18, x_19, x_20, x_21);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_23);
x_25 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkEqNDRecImp(x_15, x_23, x_16, x_17, x_18, x_19, x_20, x_24);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
x_28 = l_Lean_Meta_substCore___lambda__2(x_3, x_23, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_26, x_17, x_18, x_19, x_20, x_27);
lean_dec(x_23);
return x_28;
}
else
{
uint8_t x_29; 
lean_dec(x_23);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_29 = !lean_is_exclusive(x_25);
if (x_29 == 0)
{
return x_25;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_25, 0);
x_31 = lean_ctor_get(x_25, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_25);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
}
}
lean_object* l_Lean_Meta_substCore___lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_11 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkEqSymmImp(x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = l_Lean_Expr_replaceFVar(x_1, x_2, x_12);
lean_dec(x_12);
x_15 = lean_array_push(x_3, x_4);
x_16 = lean_array_push(x_15, x_5);
x_17 = l_Lean_Meta_mkLambdaFVars___at_Lean_Meta_SynthInstance_tryResolveCore___spec__1(x_16, x_14, x_6, x_7, x_8, x_9, x_13);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
return x_17;
}
else
{
uint8_t x_18; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_18 = !lean_is_exclusive(x_11);
if (x_18 == 0)
{
return x_11;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_11, 0);
x_20 = lean_ctor_get(x_11, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_11);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
}
}
lean_object* l_Lean_Meta_substCore___lambda__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; 
x_16 = lean_array_get_size(x_1);
x_17 = lean_unsigned_to_nat(2u);
x_18 = lean_nat_sub(x_16, x_17);
lean_dec(x_16);
x_19 = 1;
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
x_20 = l_Lean_Meta_introNCore(x_10, x_18, x_2, x_19, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = !lean_is_exclusive(x_21);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_21, 0);
x_25 = lean_array_get_size(x_24);
lean_inc(x_25);
x_26 = l_Nat_foldM_loop___at_Lean_Meta_substCore___spec__5(x_1, x_24, x_25, x_25, x_3, x_11, x_12, x_13, x_14, x_22);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_25);
lean_dec(x_24);
if (x_4 == 0)
{
uint8_t x_27; 
lean_dec(x_9);
x_27 = !lean_is_exclusive(x_26);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_26, 0);
x_29 = l_Lean_Meta_FVarSubst_insert(x_28, x_5, x_6);
x_30 = l_Lean_Meta_FVarSubst_insert(x_29, x_7, x_8);
lean_ctor_set(x_21, 0, x_30);
lean_ctor_set(x_26, 0, x_21);
return x_26;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_31 = lean_ctor_get(x_26, 0);
x_32 = lean_ctor_get(x_26, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_26);
x_33 = l_Lean_Meta_FVarSubst_insert(x_31, x_5, x_6);
x_34 = l_Lean_Meta_FVarSubst_insert(x_33, x_7, x_8);
lean_ctor_set(x_21, 0, x_34);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_21);
lean_ctor_set(x_35, 1, x_32);
return x_35;
}
}
else
{
uint8_t x_36; 
lean_dec(x_6);
x_36 = !lean_is_exclusive(x_26);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_26, 0);
x_38 = l_Lean_Meta_FVarSubst_insert(x_37, x_5, x_9);
x_39 = l_Lean_Meta_FVarSubst_insert(x_38, x_7, x_8);
lean_ctor_set(x_21, 0, x_39);
lean_ctor_set(x_26, 0, x_21);
return x_26;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_40 = lean_ctor_get(x_26, 0);
x_41 = lean_ctor_get(x_26, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_26);
x_42 = l_Lean_Meta_FVarSubst_insert(x_40, x_5, x_9);
x_43 = l_Lean_Meta_FVarSubst_insert(x_42, x_7, x_8);
lean_ctor_set(x_21, 0, x_43);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_21);
lean_ctor_set(x_44, 1, x_41);
return x_44;
}
}
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_45 = lean_ctor_get(x_21, 0);
x_46 = lean_ctor_get(x_21, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_21);
x_47 = lean_array_get_size(x_45);
lean_inc(x_47);
x_48 = l_Nat_foldM_loop___at_Lean_Meta_substCore___spec__5(x_1, x_45, x_47, x_47, x_3, x_11, x_12, x_13, x_14, x_22);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_47);
lean_dec(x_45);
if (x_4 == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
lean_dec(x_9);
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_48, 1);
lean_inc(x_50);
if (lean_is_exclusive(x_48)) {
 lean_ctor_release(x_48, 0);
 lean_ctor_release(x_48, 1);
 x_51 = x_48;
} else {
 lean_dec_ref(x_48);
 x_51 = lean_box(0);
}
x_52 = l_Lean_Meta_FVarSubst_insert(x_49, x_5, x_6);
x_53 = l_Lean_Meta_FVarSubst_insert(x_52, x_7, x_8);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_46);
if (lean_is_scalar(x_51)) {
 x_55 = lean_alloc_ctor(0, 2, 0);
} else {
 x_55 = x_51;
}
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_50);
return x_55;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
lean_dec(x_6);
x_56 = lean_ctor_get(x_48, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_48, 1);
lean_inc(x_57);
if (lean_is_exclusive(x_48)) {
 lean_ctor_release(x_48, 0);
 lean_ctor_release(x_48, 1);
 x_58 = x_48;
} else {
 lean_dec_ref(x_48);
 x_58 = lean_box(0);
}
x_59 = l_Lean_Meta_FVarSubst_insert(x_56, x_5, x_9);
x_60 = l_Lean_Meta_FVarSubst_insert(x_59, x_7, x_8);
x_61 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_46);
if (lean_is_scalar(x_58)) {
 x_62 = lean_alloc_ctor(0, 2, 0);
} else {
 x_62 = x_58;
}
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_57);
return x_62;
}
}
}
else
{
uint8_t x_63; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_63 = !lean_is_exclusive(x_20);
if (x_63 == 0)
{
return x_20;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_64 = lean_ctor_get(x_20, 0);
x_65 = lean_ctor_get(x_20, 1);
lean_inc(x_65);
lean_inc(x_64);
lean_dec(x_20);
x_66 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_66, 0, x_64);
lean_ctor_set(x_66, 1, x_65);
return x_66;
}
}
}
}
lean_object* l_Lean_Meta_substCore___lambda__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18, lean_object* x_19) {
_start:
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = l_Lean_Meta_assignExprMVar___at___private_Lean_Meta_InferType_0__Lean_Meta_getLevelImp___spec__3(x_1, x_14, x_15, x_16, x_17, x_18, x_19);
x_21 = lean_ctor_get(x_20, 1);
lean_inc(x_21);
lean_dec(x_20);
x_22 = l_Lean_Expr_mvarId_x21(x_2);
if (x_6 == 0)
{
lean_object* x_23; 
lean_dec(x_13);
lean_dec(x_12);
x_23 = l_Lean_Meta_substCore___lambda__5(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_22, x_15, x_16, x_17, x_18, x_21);
return x_23;
}
else
{
lean_object* x_24; 
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
x_24 = l_Lean_Meta_clear(x_22, x_12, x_15, x_16, x_17, x_18, x_21);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
x_27 = l_Lean_Meta_clear(x_25, x_13, x_15, x_16, x_17, x_18, x_26);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
x_30 = l_Lean_Meta_substCore___lambda__5(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_28, x_15, x_16, x_17, x_18, x_29);
return x_30;
}
else
{
uint8_t x_31; 
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
x_31 = !lean_is_exclusive(x_27);
if (x_31 == 0)
{
return x_27;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_27, 0);
x_33 = lean_ctor_get(x_27, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_27);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
}
else
{
uint8_t x_35; 
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
x_35 = !lean_is_exclusive(x_24);
if (x_35 == 0)
{
return x_24;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_24, 0);
x_37 = lean_ctor_get(x_24, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_24);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
}
}
}
lean_object* l_Lean_Meta_substCore___lambda__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, uint8_t x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18, lean_object* x_19, lean_object* x_20, lean_object* x_21) {
_start:
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
lean_inc(x_17);
x_22 = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(x_1, x_2, x_17, x_18, x_19, x_20, x_21);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_23);
x_25 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkEqRecImp(x_15, x_23, x_16, x_17, x_18, x_19, x_20, x_24);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
x_28 = l_Lean_Meta_substCore___lambda__6(x_3, x_23, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_26, x_17, x_18, x_19, x_20, x_27);
lean_dec(x_23);
return x_28;
}
else
{
uint8_t x_29; 
lean_dec(x_23);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_29 = !lean_is_exclusive(x_25);
if (x_29 == 0)
{
return x_25;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_25, 0);
x_31 = lean_ctor_get(x_25, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_25);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
}
}
lean_object* l_Lean_Meta_substCore___lambda__8(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; 
x_16 = lean_array_get_size(x_1);
x_17 = lean_unsigned_to_nat(2u);
x_18 = lean_nat_sub(x_16, x_17);
lean_dec(x_16);
x_19 = 1;
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
x_20 = l_Lean_Meta_introNCore(x_10, x_18, x_2, x_19, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = !lean_is_exclusive(x_21);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_21, 0);
x_25 = lean_array_get_size(x_24);
lean_inc(x_25);
x_26 = l_Nat_foldM_loop___at_Lean_Meta_substCore___spec__7(x_1, x_24, x_25, x_25, x_3, x_11, x_12, x_13, x_14, x_22);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_25);
lean_dec(x_24);
if (x_4 == 0)
{
uint8_t x_27; 
lean_dec(x_9);
x_27 = !lean_is_exclusive(x_26);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_26, 0);
x_29 = l_Lean_Meta_FVarSubst_insert(x_28, x_5, x_6);
x_30 = l_Lean_Meta_FVarSubst_insert(x_29, x_7, x_8);
lean_ctor_set(x_21, 0, x_30);
lean_ctor_set(x_26, 0, x_21);
return x_26;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_31 = lean_ctor_get(x_26, 0);
x_32 = lean_ctor_get(x_26, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_26);
x_33 = l_Lean_Meta_FVarSubst_insert(x_31, x_5, x_6);
x_34 = l_Lean_Meta_FVarSubst_insert(x_33, x_7, x_8);
lean_ctor_set(x_21, 0, x_34);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_21);
lean_ctor_set(x_35, 1, x_32);
return x_35;
}
}
else
{
uint8_t x_36; 
lean_dec(x_6);
x_36 = !lean_is_exclusive(x_26);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_26, 0);
x_38 = l_Lean_Meta_FVarSubst_insert(x_37, x_5, x_9);
x_39 = l_Lean_Meta_FVarSubst_insert(x_38, x_7, x_8);
lean_ctor_set(x_21, 0, x_39);
lean_ctor_set(x_26, 0, x_21);
return x_26;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_40 = lean_ctor_get(x_26, 0);
x_41 = lean_ctor_get(x_26, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_26);
x_42 = l_Lean_Meta_FVarSubst_insert(x_40, x_5, x_9);
x_43 = l_Lean_Meta_FVarSubst_insert(x_42, x_7, x_8);
lean_ctor_set(x_21, 0, x_43);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_21);
lean_ctor_set(x_44, 1, x_41);
return x_44;
}
}
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_45 = lean_ctor_get(x_21, 0);
x_46 = lean_ctor_get(x_21, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_21);
x_47 = lean_array_get_size(x_45);
lean_inc(x_47);
x_48 = l_Nat_foldM_loop___at_Lean_Meta_substCore___spec__7(x_1, x_45, x_47, x_47, x_3, x_11, x_12, x_13, x_14, x_22);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_47);
lean_dec(x_45);
if (x_4 == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
lean_dec(x_9);
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_48, 1);
lean_inc(x_50);
if (lean_is_exclusive(x_48)) {
 lean_ctor_release(x_48, 0);
 lean_ctor_release(x_48, 1);
 x_51 = x_48;
} else {
 lean_dec_ref(x_48);
 x_51 = lean_box(0);
}
x_52 = l_Lean_Meta_FVarSubst_insert(x_49, x_5, x_6);
x_53 = l_Lean_Meta_FVarSubst_insert(x_52, x_7, x_8);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_46);
if (lean_is_scalar(x_51)) {
 x_55 = lean_alloc_ctor(0, 2, 0);
} else {
 x_55 = x_51;
}
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_50);
return x_55;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
lean_dec(x_6);
x_56 = lean_ctor_get(x_48, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_48, 1);
lean_inc(x_57);
if (lean_is_exclusive(x_48)) {
 lean_ctor_release(x_48, 0);
 lean_ctor_release(x_48, 1);
 x_58 = x_48;
} else {
 lean_dec_ref(x_48);
 x_58 = lean_box(0);
}
x_59 = l_Lean_Meta_FVarSubst_insert(x_56, x_5, x_9);
x_60 = l_Lean_Meta_FVarSubst_insert(x_59, x_7, x_8);
x_61 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_46);
if (lean_is_scalar(x_58)) {
 x_62 = lean_alloc_ctor(0, 2, 0);
} else {
 x_62 = x_58;
}
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_57);
return x_62;
}
}
}
else
{
uint8_t x_63; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_63 = !lean_is_exclusive(x_20);
if (x_63 == 0)
{
return x_20;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_64 = lean_ctor_get(x_20, 0);
x_65 = lean_ctor_get(x_20, 1);
lean_inc(x_65);
lean_inc(x_64);
lean_dec(x_20);
x_66 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_66, 0, x_64);
lean_ctor_set(x_66, 1, x_65);
return x_66;
}
}
}
}
lean_object* l_Lean_Meta_substCore___lambda__9(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18, lean_object* x_19) {
_start:
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = l_Lean_Meta_assignExprMVar___at___private_Lean_Meta_InferType_0__Lean_Meta_getLevelImp___spec__3(x_1, x_14, x_15, x_16, x_17, x_18, x_19);
x_21 = lean_ctor_get(x_20, 1);
lean_inc(x_21);
lean_dec(x_20);
x_22 = l_Lean_Expr_mvarId_x21(x_2);
if (x_6 == 0)
{
lean_object* x_23; 
lean_dec(x_13);
lean_dec(x_12);
x_23 = l_Lean_Meta_substCore___lambda__8(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_22, x_15, x_16, x_17, x_18, x_21);
return x_23;
}
else
{
lean_object* x_24; 
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
x_24 = l_Lean_Meta_clear(x_22, x_12, x_15, x_16, x_17, x_18, x_21);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
x_27 = l_Lean_Meta_clear(x_25, x_13, x_15, x_16, x_17, x_18, x_26);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
x_30 = l_Lean_Meta_substCore___lambda__8(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_28, x_15, x_16, x_17, x_18, x_29);
return x_30;
}
else
{
uint8_t x_31; 
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
x_31 = !lean_is_exclusive(x_27);
if (x_31 == 0)
{
return x_27;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_27, 0);
x_33 = lean_ctor_get(x_27, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_27);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
}
else
{
uint8_t x_35; 
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
x_35 = !lean_is_exclusive(x_24);
if (x_35 == 0)
{
return x_24;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_24, 0);
x_37 = lean_ctor_get(x_24, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_24);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
}
}
}
lean_object* l_Lean_Meta_substCore___lambda__10(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, uint8_t x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18, lean_object* x_19, lean_object* x_20, lean_object* x_21) {
_start:
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
lean_inc(x_17);
x_22 = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(x_1, x_2, x_17, x_18, x_19, x_20, x_21);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_23);
x_25 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkEqRecImp(x_15, x_23, x_16, x_17, x_18, x_19, x_20, x_24);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
x_28 = l_Lean_Meta_substCore___lambda__9(x_3, x_23, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_26, x_17, x_18, x_19, x_20, x_27);
lean_dec(x_23);
return x_28;
}
else
{
uint8_t x_29; 
lean_dec(x_23);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_29 = !lean_is_exclusive(x_25);
if (x_29 == 0)
{
return x_25;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_25, 0);
x_31 = lean_ctor_get(x_25, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_25);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
}
}
static lean_object* _init_l_Lean_Meta_substCore___lambda__11___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("_h");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_substCore___lambda__11___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_substCore___lambda__11___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_substCore___lambda__11___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Lean.Meta.Tactic.Subst");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_substCore___lambda__11___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Lean.Meta.substCore");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_substCore___lambda__11___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Meta_substCore___lambda__11___closed__3;
x_2 = l_Lean_Meta_substCore___lambda__11___closed__4;
x_3 = lean_unsigned_to_nat(48u);
x_4 = lean_unsigned_to_nat(20u);
x_5 = l_Lean_Name_getString_x21___closed__3;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
lean_object* l_Lean_Meta_substCore___lambda__11(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, uint8_t x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, uint8_t x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18, lean_object* x_19, lean_object* x_20) {
_start:
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_15, 2);
lean_inc(x_21);
lean_dec(x_15);
lean_inc(x_16);
lean_inc(x_1);
x_22 = l_Lean_Meta_getLocalDecl___at_Lean_Meta_getFVarLocalDecl___spec__1(x_1, x_16, x_17, x_18, x_19, x_20);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = l_Lean_LocalDecl_type(x_23);
lean_dec(x_23);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
x_26 = l_Lean_Meta_matchEq_x3f(x_25, x_16, x_17, x_18, x_19, x_24);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; 
lean_dec(x_21);
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_100 = l_Lean_Meta_throwLetTypeMismatchMessage___rarg___closed__1;
x_101 = l_Lean_Meta_substCore___lambda__11___closed__5;
x_102 = lean_panic_fn(x_100, x_101);
x_103 = lean_apply_5(x_102, x_16, x_17, x_18, x_19, x_28);
return x_103;
}
else
{
lean_object* x_104; lean_object* x_105; 
x_104 = lean_ctor_get(x_27, 0);
lean_inc(x_104);
lean_dec(x_27);
x_105 = lean_ctor_get(x_104, 1);
lean_inc(x_105);
lean_dec(x_104);
if (x_13 == 0)
{
lean_object* x_106; 
x_106 = lean_ctor_get(x_105, 1);
lean_inc(x_106);
lean_dec(x_105);
x_29 = x_106;
goto block_99;
}
else
{
lean_object* x_107; 
x_107 = lean_ctor_get(x_105, 0);
lean_inc(x_107);
lean_dec(x_105);
x_29 = x_107;
goto block_99;
}
}
block_99:
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_30 = lean_st_ref_get(x_17, x_28);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = lean_ctor_get(x_31, 0);
lean_inc(x_33);
lean_dec(x_31);
lean_inc(x_21);
x_34 = l_Lean_MetavarContext_exprDependsOn(x_33, x_21, x_1);
x_35 = lean_unbox(x_34);
lean_dec(x_34);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
lean_dec(x_14);
x_36 = l_Lean_mkOptionalNode___closed__2;
lean_inc(x_2);
x_37 = lean_array_push(x_36, x_2);
lean_inc(x_16);
lean_inc(x_21);
x_38 = l_Lean_Meta_mkLambdaFVars___at_Lean_Meta_SynthInstance_tryResolveCore___spec__1(x_37, x_21, x_16, x_17, x_18, x_19, x_32);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
lean_dec(x_38);
lean_inc(x_2);
x_41 = l_Lean_Expr_replaceFVar(x_21, x_2, x_29);
lean_dec(x_21);
if (x_13 == 0)
{
lean_object* x_42; 
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_11);
x_42 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkEqSymmImp(x_11, x_16, x_17, x_18, x_19, x_40);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
lean_dec(x_42);
x_45 = l_Lean_Meta_substCore___lambda__3(x_41, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_2, x_10, x_11, x_29, x_1, x_12, x_39, x_43, x_16, x_17, x_18, x_19, x_44);
return x_45;
}
else
{
uint8_t x_46; 
lean_dec(x_41);
lean_dec(x_39);
lean_dec(x_29);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_46 = !lean_is_exclusive(x_42);
if (x_46 == 0)
{
return x_42;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_42, 0);
x_48 = lean_ctor_get(x_42, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_42);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
}
}
else
{
lean_object* x_50; 
lean_inc(x_11);
x_50 = l_Lean_Meta_substCore___lambda__3(x_41, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_2, x_10, x_11, x_29, x_1, x_12, x_39, x_11, x_16, x_17, x_18, x_19, x_40);
return x_50;
}
}
else
{
uint8_t x_51; 
lean_dec(x_29);
lean_dec(x_21);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_51 = !lean_is_exclusive(x_38);
if (x_51 == 0)
{
return x_38;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_38, 0);
x_53 = lean_ctor_get(x_38, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_38);
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
return x_54;
}
}
}
else
{
lean_object* x_55; lean_object* x_56; 
lean_inc(x_2);
x_55 = l_Lean_Expr_replaceFVar(x_21, x_2, x_29);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_29);
x_56 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkEqReflImp(x_29, x_16, x_17, x_18, x_19, x_32);
if (lean_obj_tag(x_56) == 0)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_56, 1);
lean_inc(x_58);
lean_dec(x_56);
lean_inc(x_11);
x_59 = l_Lean_Expr_replaceFVar(x_55, x_11, x_57);
lean_dec(x_57);
lean_dec(x_55);
if (x_13 == 0)
{
lean_object* x_60; 
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_2);
lean_inc(x_29);
x_60 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkEqImp(x_29, x_2, x_16, x_17, x_18, x_19, x_58);
if (lean_obj_tag(x_60) == 0)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; uint8_t x_65; lean_object* x_66; 
x_61 = lean_ctor_get(x_60, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_60, 1);
lean_inc(x_62);
lean_dec(x_60);
lean_inc(x_2);
lean_inc(x_11);
x_63 = lean_alloc_closure((void*)(l_Lean_Meta_substCore___lambda__4___boxed), 10, 4);
lean_closure_set(x_63, 0, x_21);
lean_closure_set(x_63, 1, x_11);
lean_closure_set(x_63, 2, x_14);
lean_closure_set(x_63, 3, x_2);
x_64 = l_Lean_Meta_substCore___lambda__11___closed__2;
x_65 = 0;
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
x_66 = l_Lean_Meta_withLocalDecl___at_Lean_Meta_substCore___spec__4___rarg(x_64, x_65, x_61, x_63, x_16, x_17, x_18, x_19, x_62);
if (lean_obj_tag(x_66) == 0)
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_67 = lean_ctor_get(x_66, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_66, 1);
lean_inc(x_68);
lean_dec(x_66);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_11);
x_69 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkEqSymmImp(x_11, x_16, x_17, x_18, x_19, x_68);
if (lean_obj_tag(x_69) == 0)
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_70 = lean_ctor_get(x_69, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_69, 1);
lean_inc(x_71);
lean_dec(x_69);
x_72 = l_Lean_Meta_substCore___lambda__7(x_59, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_2, x_10, x_11, x_29, x_1, x_12, x_67, x_70, x_16, x_17, x_18, x_19, x_71);
return x_72;
}
else
{
uint8_t x_73; 
lean_dec(x_67);
lean_dec(x_59);
lean_dec(x_29);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_73 = !lean_is_exclusive(x_69);
if (x_73 == 0)
{
return x_69;
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_74 = lean_ctor_get(x_69, 0);
x_75 = lean_ctor_get(x_69, 1);
lean_inc(x_75);
lean_inc(x_74);
lean_dec(x_69);
x_76 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_76, 0, x_74);
lean_ctor_set(x_76, 1, x_75);
return x_76;
}
}
}
else
{
uint8_t x_77; 
lean_dec(x_59);
lean_dec(x_29);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_77 = !lean_is_exclusive(x_66);
if (x_77 == 0)
{
return x_66;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_78 = lean_ctor_get(x_66, 0);
x_79 = lean_ctor_get(x_66, 1);
lean_inc(x_79);
lean_inc(x_78);
lean_dec(x_66);
x_80 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_80, 0, x_78);
lean_ctor_set(x_80, 1, x_79);
return x_80;
}
}
}
else
{
uint8_t x_81; 
lean_dec(x_59);
lean_dec(x_29);
lean_dec(x_21);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_81 = !lean_is_exclusive(x_60);
if (x_81 == 0)
{
return x_60;
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_82 = lean_ctor_get(x_60, 0);
x_83 = lean_ctor_get(x_60, 1);
lean_inc(x_83);
lean_inc(x_82);
lean_dec(x_60);
x_84 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_84, 0, x_82);
lean_ctor_set(x_84, 1, x_83);
return x_84;
}
}
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; 
lean_inc(x_2);
x_85 = lean_array_push(x_14, x_2);
lean_inc(x_11);
x_86 = lean_array_push(x_85, x_11);
lean_inc(x_16);
x_87 = l_Lean_Meta_mkLambdaFVars___at_Lean_Meta_SynthInstance_tryResolveCore___spec__1(x_86, x_21, x_16, x_17, x_18, x_19, x_58);
if (lean_obj_tag(x_87) == 0)
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_88 = lean_ctor_get(x_87, 0);
lean_inc(x_88);
x_89 = lean_ctor_get(x_87, 1);
lean_inc(x_89);
lean_dec(x_87);
lean_inc(x_11);
x_90 = l_Lean_Meta_substCore___lambda__10(x_59, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_2, x_10, x_11, x_29, x_1, x_12, x_88, x_11, x_16, x_17, x_18, x_19, x_89);
return x_90;
}
else
{
uint8_t x_91; 
lean_dec(x_59);
lean_dec(x_29);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_91 = !lean_is_exclusive(x_87);
if (x_91 == 0)
{
return x_87;
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_92 = lean_ctor_get(x_87, 0);
x_93 = lean_ctor_get(x_87, 1);
lean_inc(x_93);
lean_inc(x_92);
lean_dec(x_87);
x_94 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_94, 0, x_92);
lean_ctor_set(x_94, 1, x_93);
return x_94;
}
}
}
}
else
{
uint8_t x_95; 
lean_dec(x_55);
lean_dec(x_29);
lean_dec(x_21);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_95 = !lean_is_exclusive(x_56);
if (x_95 == 0)
{
return x_56;
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_96 = lean_ctor_get(x_56, 0);
x_97 = lean_ctor_get(x_56, 1);
lean_inc(x_97);
lean_inc(x_96);
lean_dec(x_56);
x_98 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_98, 0, x_96);
lean_ctor_set(x_98, 1, x_97);
return x_98;
}
}
}
}
}
else
{
uint8_t x_108; 
lean_dec(x_21);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_108 = !lean_is_exclusive(x_26);
if (x_108 == 0)
{
return x_26;
}
else
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_109 = lean_ctor_get(x_26, 0);
x_110 = lean_ctor_get(x_26, 1);
lean_inc(x_110);
lean_inc(x_109);
lean_dec(x_26);
x_111 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_111, 0, x_109);
lean_ctor_set(x_111, 1, x_110);
return x_111;
}
}
}
else
{
uint8_t x_112; 
lean_dec(x_21);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_112 = !lean_is_exclusive(x_22);
if (x_112 == 0)
{
return x_22;
}
else
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_113 = lean_ctor_get(x_22, 0);
x_114 = lean_ctor_get(x_22, 1);
lean_inc(x_114);
lean_inc(x_113);
lean_dec(x_22);
x_115 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_115, 0, x_113);
lean_ctor_set(x_115, 1, x_114);
return x_115;
}
}
}
}
static lean_object* _init_l_Lean_Meta_substCore___lambda__12___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("reverted variables ");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_substCore___lambda__12___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_substCore___lambda__12___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
lean_object* l_Lean_Meta_substCore___lambda__12(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, uint8_t x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
lean_inc(x_10);
lean_inc(x_1);
x_15 = l_Lean_Meta_getLocalDecl___at_Lean_Meta_getFVarLocalDecl___spec__1(x_1, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; 
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec(x_15);
x_17 = l_Lean_Syntax_mkApp___closed__1;
lean_inc(x_1);
x_18 = lean_array_push(x_17, x_1);
lean_inc(x_2);
x_19 = lean_array_push(x_18, x_2);
x_20 = 1;
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_21 = l_Lean_Meta_revert(x_3, x_19, x_20, x_10, x_11, x_12, x_13, x_16);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = lean_ctor_get(x_22, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_22, 1);
lean_inc(x_25);
lean_dec(x_22);
x_26 = lean_box(0);
x_27 = lean_unsigned_to_nat(2u);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_28 = l_Lean_Meta_introNCore(x_25, x_27, x_26, x_20, x_10, x_11, x_12, x_13, x_23);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_48; lean_object* x_49; lean_object* x_60; lean_object* x_61; lean_object* x_62; uint8_t x_63; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
x_31 = lean_ctor_get(x_29, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_29, 1);
lean_inc(x_32);
lean_dec(x_29);
x_60 = lean_st_ref_get(x_13, x_30);
x_61 = lean_ctor_get(x_60, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_61, 3);
lean_inc(x_62);
lean_dec(x_61);
x_63 = lean_ctor_get_uint8(x_62, sizeof(void*)*1);
lean_dec(x_62);
if (x_63 == 0)
{
lean_object* x_64; uint8_t x_65; 
x_64 = lean_ctor_get(x_60, 1);
lean_inc(x_64);
lean_dec(x_60);
x_65 = 0;
x_48 = x_65;
x_49 = x_64;
goto block_59;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; uint8_t x_70; 
x_66 = lean_ctor_get(x_60, 1);
lean_inc(x_66);
lean_dec(x_60);
lean_inc(x_8);
x_67 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Meta_isLevelDefEqAux___spec__2(x_8, x_10, x_11, x_12, x_13, x_66);
x_68 = lean_ctor_get(x_67, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_67, 1);
lean_inc(x_69);
lean_dec(x_67);
x_70 = lean_unbox(x_68);
lean_dec(x_68);
x_48 = x_70;
x_49 = x_69;
goto block_59;
}
block_47:
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_34 = l_Lean_Init_Prelude___instance__67;
x_35 = lean_unsigned_to_nat(0u);
x_36 = lean_array_get(x_34, x_31, x_35);
lean_inc(x_36);
x_37 = l_Lean_mkFVar(x_36);
x_38 = lean_unsigned_to_nat(1u);
x_39 = lean_array_get(x_34, x_31, x_38);
lean_dec(x_31);
lean_inc(x_39);
x_40 = l_Lean_mkFVar(x_39);
lean_inc(x_32);
x_41 = lean_alloc_closure((void*)(l_Lean_Meta_getMVarDecl___at_Lean_Meta_isReadOnlyExprMVar___spec__1___boxed), 6, 1);
lean_closure_set(x_41, 0, x_32);
x_42 = lean_box(x_6);
x_43 = lean_box(x_7);
lean_inc(x_32);
x_44 = lean_alloc_closure((void*)(l_Lean_Meta_substCore___lambda__11___boxed), 20, 14);
lean_closure_set(x_44, 0, x_39);
lean_closure_set(x_44, 1, x_37);
lean_closure_set(x_44, 2, x_4);
lean_closure_set(x_44, 3, x_32);
lean_closure_set(x_44, 4, x_24);
lean_closure_set(x_44, 5, x_26);
lean_closure_set(x_44, 6, x_5);
lean_closure_set(x_44, 7, x_42);
lean_closure_set(x_44, 8, x_1);
lean_closure_set(x_44, 9, x_2);
lean_closure_set(x_44, 10, x_40);
lean_closure_set(x_44, 11, x_36);
lean_closure_set(x_44, 12, x_43);
lean_closure_set(x_44, 13, x_17);
x_45 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_Lean_Meta_Basic___instance__8___spec__2___rarg), 7, 2);
lean_closure_set(x_45, 0, x_41);
lean_closure_set(x_45, 1, x_44);
x_46 = l_Lean_Meta_withMVarContext___at_Lean_Meta_revert___spec__5___rarg(x_32, x_45, x_10, x_11, x_12, x_13, x_33);
return x_46;
}
block_59:
{
if (x_48 == 0)
{
lean_dec(x_8);
x_33 = x_49;
goto block_47;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_50 = l_Array_toList___rarg(x_24);
x_51 = l_List_map___at_Lean_Meta_substCore___spec__8(x_50);
x_52 = l_Lean_MessageData_ofList(x_51);
lean_dec(x_51);
x_53 = l_Lean_Meta_substCore___lambda__12___closed__2;
x_54 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_52);
x_55 = l_Array_foldlMUnsafe_fold___at_Lean_withNestedTraces___spec__5___closed__1;
x_56 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
x_57 = l_Lean_addTrace___at_Lean_Meta_isLevelDefEqAux___spec__1(x_8, x_56, x_10, x_11, x_12, x_13, x_49);
x_58 = lean_ctor_get(x_57, 1);
lean_inc(x_58);
lean_dec(x_57);
x_33 = x_58;
goto block_47;
}
}
}
else
{
uint8_t x_71; 
lean_dec(x_24);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_71 = !lean_is_exclusive(x_28);
if (x_71 == 0)
{
return x_28;
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_72 = lean_ctor_get(x_28, 0);
x_73 = lean_ctor_get(x_28, 1);
lean_inc(x_73);
lean_inc(x_72);
lean_dec(x_28);
x_74 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_74, 0, x_72);
lean_ctor_set(x_74, 1, x_73);
return x_74;
}
}
}
else
{
uint8_t x_75; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_75 = !lean_is_exclusive(x_21);
if (x_75 == 0)
{
return x_21;
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_76 = lean_ctor_get(x_21, 0);
x_77 = lean_ctor_get(x_21, 1);
lean_inc(x_77);
lean_inc(x_76);
lean_dec(x_21);
x_78 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_78, 0, x_76);
lean_ctor_set(x_78, 1, x_77);
return x_78;
}
}
}
else
{
uint8_t x_79; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_79 = !lean_is_exclusive(x_15);
if (x_79 == 0)
{
return x_15;
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_80 = lean_ctor_get(x_15, 0);
x_81 = lean_ctor_get(x_15, 1);
lean_inc(x_81);
lean_inc(x_80);
lean_dec(x_15);
x_82 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_82, 0, x_80);
lean_ctor_set(x_82, 1, x_81);
return x_82;
}
}
}
}
static lean_object* _init_l_Lean_Meta_substCore___lambda__13___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("subst");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_substCore___lambda__13___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_substCore___lambda__13___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_substCore___lambda__13___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("argument must be an equality proof");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_substCore___lambda__13___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_substCore___lambda__13___closed__3;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_substCore___lambda__13___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_substCore___lambda__13___closed__4;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_substCore___lambda__13___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid equality proof, it is not of the form ");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_substCore___lambda__13___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_substCore___lambda__13___closed__6;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_substCore___lambda__13___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("\nafter WHNF, variable expected, but obtained");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_substCore___lambda__13___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_substCore___lambda__13___closed__8;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_substCore___lambda__13___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("(x = t)");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_substCore___lambda__13___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_substCore___lambda__13___closed__10;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_substCore___lambda__13___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_substCore___lambda__13___closed__7;
x_2 = l_Lean_Meta_substCore___lambda__13___closed__11;
x_3 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_substCore___lambda__13___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_substCore___lambda__13___closed__12;
x_2 = l_Array_foldlMUnsafe_fold___at_Lean_withNestedTraces___spec__5___closed__1;
x_3 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_substCore___lambda__13___closed__14() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("(t = x)");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_substCore___lambda__13___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_substCore___lambda__13___closed__14;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_substCore___lambda__13___closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_substCore___lambda__13___closed__7;
x_2 = l_Lean_Meta_substCore___lambda__13___closed__15;
x_3 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_substCore___lambda__13___closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_substCore___lambda__13___closed__16;
x_2 = l_Array_foldlMUnsafe_fold___at_Lean_withNestedTraces___spec__5___closed__1;
x_3 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_substCore___lambda__13___closed__18() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Util___hyg_225____closed__1;
x_2 = l_Lean_Meta_substCore___lambda__13___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_substCore___lambda__13___closed__19() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("' occurs at");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_substCore___lambda__13___closed__20() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_substCore___lambda__13___closed__19;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_substCore___lambda__13___closed__21() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("substituting ");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_substCore___lambda__13___closed__22() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_substCore___lambda__13___closed__21;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_substCore___lambda__13___closed__23() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(" (id: ");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_substCore___lambda__13___closed__24() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_substCore___lambda__13___closed__23;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_substCore___lambda__13___closed__25() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(" with ");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_substCore___lambda__13___closed__26() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_substCore___lambda__13___closed__25;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
lean_object* l_Lean_Meta_substCore___lambda__13(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; 
x_12 = l_Lean_Meta_substCore___lambda__13___closed__2;
lean_inc(x_1);
x_13 = l_Lean_Meta_checkNotAssigned(x_1, x_12, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
lean_dec(x_13);
lean_inc(x_7);
lean_inc(x_2);
x_15 = l_Lean_Meta_getLocalDecl___at_Lean_Meta_getFVarLocalDecl___spec__1(x_2, x_7, x_8, x_9, x_10, x_14);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = l_Lean_LocalDecl_type(x_16);
lean_dec(x_16);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_18);
x_19 = l_Lean_Meta_matchEq_x3f(x_18, x_7, x_8, x_9, x_10, x_17);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
lean_dec(x_18);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = l_Lean_Meta_substCore___lambda__13___closed__5;
x_23 = lean_box(0);
x_24 = l_Lean_Meta_throwTacticEx___rarg(x_12, x_1, x_22, x_23, x_7, x_8, x_9, x_10, x_21);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
return x_24;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_25 = lean_ctor_get(x_20, 0);
lean_inc(x_25);
lean_dec(x_20);
x_26 = lean_ctor_get(x_25, 1);
lean_inc(x_26);
lean_dec(x_25);
x_27 = lean_ctor_get(x_19, 1);
lean_inc(x_27);
lean_dec(x_19);
x_28 = lean_ctor_get(x_26, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_26, 1);
lean_inc(x_29);
lean_dec(x_26);
if (x_5 == 0)
{
uint8_t x_122; 
x_122 = 0;
x_30 = x_122;
goto block_121;
}
else
{
uint8_t x_123; 
x_123 = 1;
x_30 = x_123;
goto block_121;
}
block_121:
{
lean_object* x_31; 
if (x_30 == 0)
{
lean_inc(x_28);
x_31 = x_28;
goto block_120;
}
else
{
lean_inc(x_29);
x_31 = x_29;
goto block_120;
}
block_120:
{
lean_object* x_32; 
if (x_30 == 0)
{
lean_dec(x_28);
x_32 = x_29;
goto block_119;
}
else
{
lean_dec(x_29);
x_32 = x_28;
goto block_119;
}
block_119:
{
lean_object* x_33; 
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_33 = l_Lean_Meta_whnf___at___private_Lean_Meta_Basic_0__Lean_Meta_isClassExpensive_x3f___spec__2(x_31, x_7, x_8, x_9, x_10, x_27);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
if (lean_obj_tag(x_34) == 1)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_63; lean_object* x_64; lean_object* x_82; lean_object* x_83; lean_object* x_84; uint8_t x_85; 
lean_dec(x_18);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec(x_33);
x_36 = lean_ctor_get(x_34, 0);
lean_inc(x_36);
x_82 = lean_st_ref_get(x_10, x_35);
x_83 = lean_ctor_get(x_82, 0);
lean_inc(x_83);
x_84 = lean_ctor_get(x_83, 3);
lean_inc(x_84);
lean_dec(x_83);
x_85 = lean_ctor_get_uint8(x_84, sizeof(void*)*1);
lean_dec(x_84);
if (x_85 == 0)
{
lean_object* x_86; uint8_t x_87; 
x_86 = lean_ctor_get(x_82, 1);
lean_inc(x_86);
lean_dec(x_82);
x_87 = 0;
x_63 = x_87;
x_64 = x_86;
goto block_81;
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; uint8_t x_93; 
x_88 = lean_ctor_get(x_82, 1);
lean_inc(x_88);
lean_dec(x_82);
x_89 = l_Lean_Meta_substCore___lambda__13___closed__18;
x_90 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Meta_isLevelDefEqAux___spec__2(x_89, x_7, x_8, x_9, x_10, x_88);
x_91 = lean_ctor_get(x_90, 0);
lean_inc(x_91);
x_92 = lean_ctor_get(x_90, 1);
lean_inc(x_92);
lean_dec(x_90);
x_93 = lean_unbox(x_91);
lean_dec(x_91);
x_63 = x_93;
x_64 = x_92;
goto block_81;
}
block_62:
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; 
x_38 = lean_st_ref_get(x_8, x_37);
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
lean_dec(x_38);
x_41 = lean_ctor_get(x_39, 0);
lean_inc(x_41);
lean_dec(x_39);
lean_inc(x_32);
x_42 = l_Lean_MetavarContext_exprDependsOn(x_41, x_32, x_36);
x_43 = lean_unbox(x_42);
lean_dec(x_42);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
lean_dec(x_34);
lean_dec(x_32);
x_44 = l_Lean_Meta_substCore___lambda__13___closed__18;
x_45 = lean_box(0);
x_46 = l_Lean_Meta_substCore___lambda__12(x_36, x_2, x_1, x_6, x_3, x_4, x_30, x_44, x_45, x_7, x_8, x_9, x_10, x_40);
return x_46;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; uint8_t x_58; 
lean_dec(x_36);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
x_47 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_47, 0, x_34);
x_48 = l_Lean_throwUnknownConstant___rarg___closed__3;
x_49 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_47);
x_50 = l_Lean_Meta_substCore___lambda__13___closed__20;
x_51 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
x_52 = l_Lean_indentExpr(x_32);
x_53 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
x_54 = l_Array_foldlMUnsafe_fold___at_Lean_withNestedTraces___spec__5___closed__1;
x_55 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
x_56 = lean_box(0);
x_57 = l_Lean_Meta_throwTacticEx___rarg(x_12, x_1, x_55, x_56, x_7, x_8, x_9, x_10, x_40);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_58 = !lean_is_exclusive(x_57);
if (x_58 == 0)
{
return x_57;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_ctor_get(x_57, 0);
x_60 = lean_ctor_get(x_57, 1);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_57);
x_61 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set(x_61, 1, x_60);
return x_61;
}
}
}
block_81:
{
if (x_63 == 0)
{
x_37 = x_64;
goto block_62;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
lean_inc(x_34);
x_65 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_65, 0, x_34);
x_66 = l_Lean_Meta_substCore___lambda__13___closed__22;
x_67 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_67, 0, x_66);
lean_ctor_set(x_67, 1, x_65);
x_68 = l_Lean_Meta_substCore___lambda__13___closed__24;
x_69 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_69, 0, x_67);
lean_ctor_set(x_69, 1, x_68);
lean_inc(x_36);
x_70 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_70, 0, x_36);
x_71 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_71, 0, x_69);
lean_ctor_set(x_71, 1, x_70);
x_72 = l_Lean_Meta_substCore___lambda__13___closed__26;
x_73 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_73, 0, x_71);
lean_ctor_set(x_73, 1, x_72);
lean_inc(x_32);
x_74 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_74, 0, x_32);
x_75 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_75, 0, x_73);
lean_ctor_set(x_75, 1, x_74);
x_76 = l_Array_foldlMUnsafe_fold___at_Lean_withNestedTraces___spec__5___closed__1;
x_77 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_77, 0, x_75);
lean_ctor_set(x_77, 1, x_76);
x_78 = l_Lean_Meta_substCore___lambda__13___closed__18;
x_79 = l_Lean_addTrace___at_Lean_Meta_isLevelDefEqAux___spec__1(x_78, x_77, x_7, x_8, x_9, x_10, x_64);
x_80 = lean_ctor_get(x_79, 1);
lean_inc(x_80);
lean_dec(x_79);
x_37 = x_80;
goto block_62;
}
}
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; 
lean_dec(x_32);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
x_94 = lean_ctor_get(x_33, 1);
lean_inc(x_94);
lean_dec(x_33);
x_95 = l_Lean_indentExpr(x_18);
x_96 = l_Lean_indentExpr(x_34);
if (x_30 == 0)
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_97 = l_Lean_Meta_substCore___lambda__13___closed__13;
x_98 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_98, 0, x_97);
lean_ctor_set(x_98, 1, x_95);
x_99 = l_Lean_Meta_substCore___lambda__13___closed__9;
x_100 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_100, 0, x_98);
lean_ctor_set(x_100, 1, x_99);
x_101 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_101, 0, x_100);
lean_ctor_set(x_101, 1, x_96);
x_102 = l_Array_foldlMUnsafe_fold___at_Lean_withNestedTraces___spec__5___closed__1;
x_103 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_103, 0, x_101);
lean_ctor_set(x_103, 1, x_102);
x_104 = lean_box(0);
x_105 = l_Lean_Meta_throwTacticEx___rarg(x_12, x_1, x_103, x_104, x_7, x_8, x_9, x_10, x_94);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
return x_105;
}
else
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; 
x_106 = l_Lean_Meta_substCore___lambda__13___closed__17;
x_107 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_107, 0, x_106);
lean_ctor_set(x_107, 1, x_95);
x_108 = l_Lean_Meta_substCore___lambda__13___closed__9;
x_109 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_109, 0, x_107);
lean_ctor_set(x_109, 1, x_108);
x_110 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_110, 0, x_109);
lean_ctor_set(x_110, 1, x_96);
x_111 = l_Array_foldlMUnsafe_fold___at_Lean_withNestedTraces___spec__5___closed__1;
x_112 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_112, 0, x_110);
lean_ctor_set(x_112, 1, x_111);
x_113 = lean_box(0);
x_114 = l_Lean_Meta_throwTacticEx___rarg(x_12, x_1, x_112, x_113, x_7, x_8, x_9, x_10, x_94);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
return x_114;
}
}
}
else
{
uint8_t x_115; 
lean_dec(x_32);
lean_dec(x_18);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_115 = !lean_is_exclusive(x_33);
if (x_115 == 0)
{
return x_33;
}
else
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; 
x_116 = lean_ctor_get(x_33, 0);
x_117 = lean_ctor_get(x_33, 1);
lean_inc(x_117);
lean_inc(x_116);
lean_dec(x_33);
x_118 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_118, 0, x_116);
lean_ctor_set(x_118, 1, x_117);
return x_118;
}
}
}
}
}
}
}
else
{
uint8_t x_124; 
lean_dec(x_18);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_124 = !lean_is_exclusive(x_19);
if (x_124 == 0)
{
return x_19;
}
else
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; 
x_125 = lean_ctor_get(x_19, 0);
x_126 = lean_ctor_get(x_19, 1);
lean_inc(x_126);
lean_inc(x_125);
lean_dec(x_19);
x_127 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_127, 0, x_125);
lean_ctor_set(x_127, 1, x_126);
return x_127;
}
}
}
else
{
uint8_t x_128; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_128 = !lean_is_exclusive(x_15);
if (x_128 == 0)
{
return x_15;
}
else
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; 
x_129 = lean_ctor_get(x_15, 0);
x_130 = lean_ctor_get(x_15, 1);
lean_inc(x_130);
lean_inc(x_129);
lean_dec(x_15);
x_131 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_131, 0, x_129);
lean_ctor_set(x_131, 1, x_130);
return x_131;
}
}
}
else
{
uint8_t x_132; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_132 = !lean_is_exclusive(x_13);
if (x_132 == 0)
{
return x_13;
}
else
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; 
x_133 = lean_ctor_get(x_13, 0);
x_134 = lean_ctor_get(x_13, 1);
lean_inc(x_134);
lean_inc(x_133);
lean_dec(x_13);
x_135 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_135, 0, x_133);
lean_ctor_set(x_135, 1, x_134);
return x_135;
}
}
}
}
lean_object* l_Lean_Meta_substCore(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_inc(x_1);
x_11 = lean_alloc_closure((void*)(l_Lean_Meta_getMVarTag___boxed), 6, 1);
lean_closure_set(x_11, 0, x_1);
x_12 = lean_box(x_5);
x_13 = lean_box(x_3);
lean_inc(x_1);
x_14 = lean_alloc_closure((void*)(l_Lean_Meta_substCore___lambda__13___boxed), 11, 5);
lean_closure_set(x_14, 0, x_1);
lean_closure_set(x_14, 1, x_2);
lean_closure_set(x_14, 2, x_4);
lean_closure_set(x_14, 3, x_12);
lean_closure_set(x_14, 4, x_13);
x_15 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_Lean_Meta_Basic___instance__8___spec__2___rarg), 7, 2);
lean_closure_set(x_15, 0, x_11);
lean_closure_set(x_15, 1, x_14);
x_16 = l_Lean_Meta_withMVarContext___at_Lean_Meta_admit___spec__2___rarg(x_1, x_15, x_6, x_7, x_8, x_9, x_10);
return x_16;
}
}
lean_object* l_Nat_foldM_loop___at_Lean_Meta_substCore___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Nat_foldM_loop___at_Lean_Meta_substCore___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_11;
}
}
lean_object* l_Lean_Meta_withLocalDecl___at_Lean_Meta_substCore___spec__4___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_2);
lean_dec(x_2);
x_11 = l_Lean_Meta_withLocalDecl___at_Lean_Meta_substCore___spec__4___rarg(x_1, x_10, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
lean_object* l_Nat_foldM_loop___at_Lean_Meta_substCore___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Nat_foldM_loop___at_Lean_Meta_substCore___spec__5(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_11;
}
}
lean_object* l_Nat_foldM_loop___at_Lean_Meta_substCore___spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Nat_foldM_loop___at_Lean_Meta_substCore___spec__7(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_11;
}
}
lean_object* l_Lean_Meta_substCore___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
uint8_t x_16; lean_object* x_17; 
x_16 = lean_unbox(x_4);
lean_dec(x_4);
x_17 = l_Lean_Meta_substCore___lambda__1(x_1, x_2, x_3, x_16, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_1);
return x_17;
}
}
lean_object* l_Lean_Meta_substCore___lambda__2___boxed(lean_object** _args) {
lean_object* x_1 = _args[0];
lean_object* x_2 = _args[1];
lean_object* x_3 = _args[2];
lean_object* x_4 = _args[3];
lean_object* x_5 = _args[4];
lean_object* x_6 = _args[5];
lean_object* x_7 = _args[6];
lean_object* x_8 = _args[7];
lean_object* x_9 = _args[8];
lean_object* x_10 = _args[9];
lean_object* x_11 = _args[10];
lean_object* x_12 = _args[11];
lean_object* x_13 = _args[12];
lean_object* x_14 = _args[13];
lean_object* x_15 = _args[14];
lean_object* x_16 = _args[15];
lean_object* x_17 = _args[16];
lean_object* x_18 = _args[17];
lean_object* x_19 = _args[18];
_start:
{
uint8_t x_20; lean_object* x_21; 
x_20 = lean_unbox(x_6);
lean_dec(x_6);
x_21 = l_Lean_Meta_substCore___lambda__2(x_1, x_2, x_3, x_4, x_5, x_20, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19);
lean_dec(x_3);
lean_dec(x_2);
return x_21;
}
}
lean_object* l_Lean_Meta_substCore___lambda__3___boxed(lean_object** _args) {
lean_object* x_1 = _args[0];
lean_object* x_2 = _args[1];
lean_object* x_3 = _args[2];
lean_object* x_4 = _args[3];
lean_object* x_5 = _args[4];
lean_object* x_6 = _args[5];
lean_object* x_7 = _args[6];
lean_object* x_8 = _args[7];
lean_object* x_9 = _args[8];
lean_object* x_10 = _args[9];
lean_object* x_11 = _args[10];
lean_object* x_12 = _args[11];
lean_object* x_13 = _args[12];
lean_object* x_14 = _args[13];
lean_object* x_15 = _args[14];
lean_object* x_16 = _args[15];
lean_object* x_17 = _args[16];
lean_object* x_18 = _args[17];
lean_object* x_19 = _args[18];
lean_object* x_20 = _args[19];
lean_object* x_21 = _args[20];
_start:
{
uint8_t x_22; lean_object* x_23; 
x_22 = lean_unbox(x_7);
lean_dec(x_7);
x_23 = l_Lean_Meta_substCore___lambda__3(x_1, x_2, x_3, x_4, x_5, x_6, x_22, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_20, x_21);
lean_dec(x_4);
return x_23;
}
}
lean_object* l_Lean_Meta_substCore___lambda__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Meta_substCore___lambda__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_1);
return x_11;
}
}
lean_object* l_Lean_Meta_substCore___lambda__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
uint8_t x_16; lean_object* x_17; 
x_16 = lean_unbox(x_4);
lean_dec(x_4);
x_17 = l_Lean_Meta_substCore___lambda__5(x_1, x_2, x_3, x_16, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_1);
return x_17;
}
}
lean_object* l_Lean_Meta_substCore___lambda__6___boxed(lean_object** _args) {
lean_object* x_1 = _args[0];
lean_object* x_2 = _args[1];
lean_object* x_3 = _args[2];
lean_object* x_4 = _args[3];
lean_object* x_5 = _args[4];
lean_object* x_6 = _args[5];
lean_object* x_7 = _args[6];
lean_object* x_8 = _args[7];
lean_object* x_9 = _args[8];
lean_object* x_10 = _args[9];
lean_object* x_11 = _args[10];
lean_object* x_12 = _args[11];
lean_object* x_13 = _args[12];
lean_object* x_14 = _args[13];
lean_object* x_15 = _args[14];
lean_object* x_16 = _args[15];
lean_object* x_17 = _args[16];
lean_object* x_18 = _args[17];
lean_object* x_19 = _args[18];
_start:
{
uint8_t x_20; lean_object* x_21; 
x_20 = lean_unbox(x_6);
lean_dec(x_6);
x_21 = l_Lean_Meta_substCore___lambda__6(x_1, x_2, x_3, x_4, x_5, x_20, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19);
lean_dec(x_3);
lean_dec(x_2);
return x_21;
}
}
lean_object* l_Lean_Meta_substCore___lambda__7___boxed(lean_object** _args) {
lean_object* x_1 = _args[0];
lean_object* x_2 = _args[1];
lean_object* x_3 = _args[2];
lean_object* x_4 = _args[3];
lean_object* x_5 = _args[4];
lean_object* x_6 = _args[5];
lean_object* x_7 = _args[6];
lean_object* x_8 = _args[7];
lean_object* x_9 = _args[8];
lean_object* x_10 = _args[9];
lean_object* x_11 = _args[10];
lean_object* x_12 = _args[11];
lean_object* x_13 = _args[12];
lean_object* x_14 = _args[13];
lean_object* x_15 = _args[14];
lean_object* x_16 = _args[15];
lean_object* x_17 = _args[16];
lean_object* x_18 = _args[17];
lean_object* x_19 = _args[18];
lean_object* x_20 = _args[19];
lean_object* x_21 = _args[20];
_start:
{
uint8_t x_22; lean_object* x_23; 
x_22 = lean_unbox(x_7);
lean_dec(x_7);
x_23 = l_Lean_Meta_substCore___lambda__7(x_1, x_2, x_3, x_4, x_5, x_6, x_22, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_20, x_21);
lean_dec(x_4);
return x_23;
}
}
lean_object* l_Lean_Meta_substCore___lambda__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
uint8_t x_16; lean_object* x_17; 
x_16 = lean_unbox(x_4);
lean_dec(x_4);
x_17 = l_Lean_Meta_substCore___lambda__8(x_1, x_2, x_3, x_16, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_1);
return x_17;
}
}
lean_object* l_Lean_Meta_substCore___lambda__9___boxed(lean_object** _args) {
lean_object* x_1 = _args[0];
lean_object* x_2 = _args[1];
lean_object* x_3 = _args[2];
lean_object* x_4 = _args[3];
lean_object* x_5 = _args[4];
lean_object* x_6 = _args[5];
lean_object* x_7 = _args[6];
lean_object* x_8 = _args[7];
lean_object* x_9 = _args[8];
lean_object* x_10 = _args[9];
lean_object* x_11 = _args[10];
lean_object* x_12 = _args[11];
lean_object* x_13 = _args[12];
lean_object* x_14 = _args[13];
lean_object* x_15 = _args[14];
lean_object* x_16 = _args[15];
lean_object* x_17 = _args[16];
lean_object* x_18 = _args[17];
lean_object* x_19 = _args[18];
_start:
{
uint8_t x_20; lean_object* x_21; 
x_20 = lean_unbox(x_6);
lean_dec(x_6);
x_21 = l_Lean_Meta_substCore___lambda__9(x_1, x_2, x_3, x_4, x_5, x_20, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19);
lean_dec(x_3);
lean_dec(x_2);
return x_21;
}
}
lean_object* l_Lean_Meta_substCore___lambda__10___boxed(lean_object** _args) {
lean_object* x_1 = _args[0];
lean_object* x_2 = _args[1];
lean_object* x_3 = _args[2];
lean_object* x_4 = _args[3];
lean_object* x_5 = _args[4];
lean_object* x_6 = _args[5];
lean_object* x_7 = _args[6];
lean_object* x_8 = _args[7];
lean_object* x_9 = _args[8];
lean_object* x_10 = _args[9];
lean_object* x_11 = _args[10];
lean_object* x_12 = _args[11];
lean_object* x_13 = _args[12];
lean_object* x_14 = _args[13];
lean_object* x_15 = _args[14];
lean_object* x_16 = _args[15];
lean_object* x_17 = _args[16];
lean_object* x_18 = _args[17];
lean_object* x_19 = _args[18];
lean_object* x_20 = _args[19];
lean_object* x_21 = _args[20];
_start:
{
uint8_t x_22; lean_object* x_23; 
x_22 = lean_unbox(x_7);
lean_dec(x_7);
x_23 = l_Lean_Meta_substCore___lambda__10(x_1, x_2, x_3, x_4, x_5, x_6, x_22, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_20, x_21);
lean_dec(x_4);
return x_23;
}
}
lean_object* l_Lean_Meta_substCore___lambda__11___boxed(lean_object** _args) {
lean_object* x_1 = _args[0];
lean_object* x_2 = _args[1];
lean_object* x_3 = _args[2];
lean_object* x_4 = _args[3];
lean_object* x_5 = _args[4];
lean_object* x_6 = _args[5];
lean_object* x_7 = _args[6];
lean_object* x_8 = _args[7];
lean_object* x_9 = _args[8];
lean_object* x_10 = _args[9];
lean_object* x_11 = _args[10];
lean_object* x_12 = _args[11];
lean_object* x_13 = _args[12];
lean_object* x_14 = _args[13];
lean_object* x_15 = _args[14];
lean_object* x_16 = _args[15];
lean_object* x_17 = _args[16];
lean_object* x_18 = _args[17];
lean_object* x_19 = _args[18];
lean_object* x_20 = _args[19];
_start:
{
uint8_t x_21; uint8_t x_22; lean_object* x_23; 
x_21 = lean_unbox(x_8);
lean_dec(x_8);
x_22 = lean_unbox(x_13);
lean_dec(x_13);
x_23 = l_Lean_Meta_substCore___lambda__11(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_21, x_9, x_10, x_11, x_12, x_22, x_14, x_15, x_16, x_17, x_18, x_19, x_20);
lean_dec(x_5);
return x_23;
}
}
lean_object* l_Lean_Meta_substCore___lambda__12___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
uint8_t x_15; uint8_t x_16; lean_object* x_17; 
x_15 = lean_unbox(x_6);
lean_dec(x_6);
x_16 = lean_unbox(x_7);
lean_dec(x_7);
x_17 = l_Lean_Meta_substCore___lambda__12(x_1, x_2, x_3, x_4, x_5, x_15, x_16, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_9);
return x_17;
}
}
lean_object* l_Lean_Meta_substCore___lambda__13___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; uint8_t x_13; lean_object* x_14; 
x_12 = lean_unbox(x_4);
lean_dec(x_4);
x_13 = lean_unbox(x_5);
lean_dec(x_5);
x_14 = l_Lean_Meta_substCore___lambda__13(x_1, x_2, x_3, x_12, x_13, x_6, x_7, x_8, x_9, x_10, x_11);
return x_14;
}
}
lean_object* l_Lean_Meta_substCore___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; uint8_t x_12; lean_object* x_13; 
x_11 = lean_unbox(x_3);
lean_dec(x_3);
x_12 = lean_unbox(x_5);
lean_dec(x_5);
x_13 = l_Lean_Meta_substCore(x_1, x_2, x_11, x_4, x_12, x_6, x_7, x_8, x_9, x_10);
return x_13;
}
}
lean_object* l_Lean_Meta_subst_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; 
lean_dec(x_2);
x_4 = lean_apply_1(x_3, x_1);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
lean_dec(x_3);
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_ctor_get(x_5, 1);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 0);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_ctor_get(x_6, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_6, 1);
lean_inc(x_9);
lean_dec(x_6);
x_10 = lean_apply_3(x_2, x_7, x_8, x_9);
return x_10;
}
}
}
lean_object* l_Lean_Meta_subst_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_subst_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_subst_match__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; 
lean_dec(x_2);
x_4 = lean_apply_1(x_3, x_1);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
lean_dec(x_3);
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_apply_2(x_2, x_6, x_7);
return x_8;
}
}
}
lean_object* l_Lean_Meta_subst_match__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_subst_match__2___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_subst_match__3___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_2);
x_4 = lean_box(0);
x_5 = lean_apply_1(x_3, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
lean_dec(x_3);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_ctor_get(x_6, 1);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 0);
lean_inc(x_8);
lean_dec(x_6);
x_9 = lean_ctor_get(x_7, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_7, 1);
lean_inc(x_10);
lean_dec(x_7);
x_11 = lean_apply_3(x_2, x_8, x_9, x_10);
return x_11;
}
}
}
lean_object* l_Lean_Meta_subst_match__3(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_subst_match__3___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_subst___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, size_t x_5, size_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; 
x_13 = x_6 < x_5;
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_7);
lean_ctor_set(x_14, 1, x_12);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; 
lean_dec(x_7);
x_15 = lean_array_uget(x_4, x_6);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_2);
x_16 = l_Std_PersistentArray_findSomeMAux___at_Lean_Meta_subst___spec__3(x_1, x_2, x_15, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_15);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; size_t x_19; size_t x_20; 
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = 1;
x_20 = x_6 + x_19;
lean_inc(x_3);
{
size_t _tmp_5 = x_20;
lean_object* _tmp_6 = x_3;
lean_object* _tmp_11 = x_18;
x_6 = _tmp_5;
x_7 = _tmp_6;
x_12 = _tmp_11;
}
goto _start;
}
else
{
uint8_t x_22; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
x_22 = !lean_is_exclusive(x_16);
if (x_22 == 0)
{
lean_object* x_23; uint8_t x_24; 
x_23 = lean_ctor_get(x_16, 0);
lean_dec(x_23);
x_24 = !lean_is_exclusive(x_17);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_box(0);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_17);
lean_ctor_set(x_26, 1, x_25);
lean_ctor_set(x_16, 0, x_26);
return x_16;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_27 = lean_ctor_get(x_17, 0);
lean_inc(x_27);
lean_dec(x_17);
x_28 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_28, 0, x_27);
x_29 = lean_box(0);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
lean_ctor_set(x_16, 0, x_30);
return x_16;
}
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_31 = lean_ctor_get(x_16, 1);
lean_inc(x_31);
lean_dec(x_16);
x_32 = lean_ctor_get(x_17, 0);
lean_inc(x_32);
if (lean_is_exclusive(x_17)) {
 lean_ctor_release(x_17, 0);
 x_33 = x_17;
} else {
 lean_dec_ref(x_17);
 x_33 = lean_box(0);
}
if (lean_is_scalar(x_33)) {
 x_34 = lean_alloc_ctor(1, 1, 0);
} else {
 x_34 = x_33;
}
lean_ctor_set(x_34, 0, x_32);
x_35 = lean_box(0);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_31);
return x_37;
}
}
}
else
{
uint8_t x_38; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
x_38 = !lean_is_exclusive(x_16);
if (x_38 == 0)
{
return x_16;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_16, 0);
x_40 = lean_ctor_get(x_16, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_16);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
}
}
}
lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_subst___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, size_t x_6, size_t x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_15; uint8_t x_29; 
x_29 = x_7 < x_6;
if (x_29 == 0)
{
lean_object* x_30; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_8);
lean_ctor_set(x_30, 1, x_13);
return x_30;
}
else
{
lean_object* x_31; 
lean_dec(x_8);
x_31 = lean_array_uget(x_5, x_7);
if (lean_obj_tag(x_31) == 0)
{
lean_inc(x_3);
x_14 = x_3;
x_15 = x_13;
goto block_28;
}
else
{
uint8_t x_32; 
x_32 = !lean_is_exclusive(x_31);
if (x_32 == 0)
{
lean_object* x_33; uint8_t x_34; 
x_33 = lean_ctor_get(x_31, 0);
x_34 = l_Lean_LocalDecl_isAuxDecl(x_33);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; 
x_35 = l_Lean_LocalDecl_type(x_33);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_36 = l_Lean_Meta_matchEq_x3f(x_35, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; 
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; 
lean_free_object(x_31);
lean_dec(x_33);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
lean_dec(x_36);
lean_inc(x_3);
x_14 = x_3;
x_15 = x_38;
goto block_28;
}
else
{
lean_object* x_39; lean_object* x_40; uint8_t x_41; 
x_39 = lean_ctor_get(x_37, 0);
lean_inc(x_39);
if (lean_is_exclusive(x_37)) {
 lean_ctor_release(x_37, 0);
 x_40 = x_37;
} else {
 lean_dec_ref(x_37);
 x_40 = lean_box(0);
}
x_41 = !lean_is_exclusive(x_39);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; uint8_t x_65; 
x_42 = lean_ctor_get(x_39, 1);
x_43 = lean_ctor_get(x_39, 0);
lean_dec(x_43);
x_44 = lean_ctor_get(x_36, 1);
lean_inc(x_44);
lean_dec(x_36);
x_45 = lean_ctor_get(x_42, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_42, 1);
lean_inc(x_46);
if (lean_is_exclusive(x_42)) {
 lean_ctor_release(x_42, 0);
 lean_ctor_release(x_42, 1);
 x_47 = x_42;
} else {
 lean_dec_ref(x_42);
 x_47 = lean_box(0);
}
x_65 = l_Lean_Expr_isFVar(x_46);
if (x_65 == 0)
{
uint8_t x_66; 
lean_dec(x_47);
lean_dec(x_40);
x_66 = l_Lean_Expr_isFVar(x_45);
if (x_66 == 0)
{
lean_dec(x_46);
lean_dec(x_45);
lean_free_object(x_39);
lean_free_object(x_31);
lean_dec(x_33);
lean_inc(x_3);
x_14 = x_3;
x_15 = x_44;
goto block_28;
}
else
{
lean_object* x_67; uint8_t x_68; lean_object* x_69; uint8_t x_70; 
x_67 = l_Lean_Expr_fvarId_x21(x_45);
lean_dec(x_45);
x_68 = lean_name_eq(x_67, x_1);
lean_dec(x_67);
lean_inc(x_2);
x_69 = l_Lean_MetavarContext_exprDependsOn(x_2, x_46, x_1);
x_70 = lean_unbox(x_69);
lean_dec(x_69);
if (x_70 == 0)
{
if (x_68 == 0)
{
lean_free_object(x_39);
lean_free_object(x_31);
lean_dec(x_33);
lean_inc(x_3);
x_14 = x_3;
x_15 = x_44;
goto block_28;
}
else
{
lean_object* x_71; uint8_t x_72; lean_object* x_73; 
x_71 = l_Lean_LocalDecl_fvarId(x_33);
lean_dec(x_33);
x_72 = 0;
x_73 = lean_box(x_72);
lean_ctor_set(x_39, 1, x_73);
lean_ctor_set(x_39, 0, x_71);
lean_ctor_set(x_31, 0, x_39);
x_14 = x_31;
x_15 = x_44;
goto block_28;
}
}
else
{
lean_free_object(x_39);
lean_free_object(x_31);
lean_dec(x_33);
lean_inc(x_3);
x_14 = x_3;
x_15 = x_44;
goto block_28;
}
}
}
else
{
lean_object* x_74; uint8_t x_75; lean_object* x_76; uint8_t x_77; 
x_74 = l_Lean_Expr_fvarId_x21(x_46);
x_75 = lean_name_eq(x_74, x_1);
lean_dec(x_74);
lean_inc(x_45);
lean_inc(x_2);
x_76 = l_Lean_MetavarContext_exprDependsOn(x_2, x_45, x_1);
x_77 = lean_unbox(x_76);
lean_dec(x_76);
if (x_77 == 0)
{
if (x_75 == 0)
{
uint8_t x_78; 
lean_dec(x_47);
lean_dec(x_40);
x_78 = l_Lean_Expr_isFVar(x_45);
if (x_78 == 0)
{
lean_dec(x_46);
lean_dec(x_45);
lean_free_object(x_39);
lean_free_object(x_31);
lean_dec(x_33);
lean_inc(x_3);
x_14 = x_3;
x_15 = x_44;
goto block_28;
}
else
{
lean_object* x_79; uint8_t x_80; lean_object* x_81; uint8_t x_82; 
x_79 = l_Lean_Expr_fvarId_x21(x_45);
lean_dec(x_45);
x_80 = lean_name_eq(x_79, x_1);
lean_dec(x_79);
lean_inc(x_2);
x_81 = l_Lean_MetavarContext_exprDependsOn(x_2, x_46, x_1);
x_82 = lean_unbox(x_81);
lean_dec(x_81);
if (x_82 == 0)
{
if (x_80 == 0)
{
lean_free_object(x_39);
lean_free_object(x_31);
lean_dec(x_33);
lean_inc(x_3);
x_14 = x_3;
x_15 = x_44;
goto block_28;
}
else
{
lean_object* x_83; uint8_t x_84; lean_object* x_85; 
x_83 = l_Lean_LocalDecl_fvarId(x_33);
lean_dec(x_33);
x_84 = 0;
x_85 = lean_box(x_84);
lean_ctor_set(x_39, 1, x_85);
lean_ctor_set(x_39, 0, x_83);
lean_ctor_set(x_31, 0, x_39);
x_14 = x_31;
x_15 = x_44;
goto block_28;
}
}
else
{
lean_free_object(x_39);
lean_free_object(x_31);
lean_dec(x_33);
lean_inc(x_3);
x_14 = x_3;
x_15 = x_44;
goto block_28;
}
}
}
else
{
uint8_t x_86; 
lean_free_object(x_39);
lean_free_object(x_31);
x_86 = 1;
x_48 = x_86;
goto block_64;
}
}
else
{
if (x_75 == 0)
{
uint8_t x_87; 
lean_dec(x_47);
lean_dec(x_40);
x_87 = l_Lean_Expr_isFVar(x_45);
if (x_87 == 0)
{
lean_dec(x_46);
lean_dec(x_45);
lean_free_object(x_39);
lean_free_object(x_31);
lean_dec(x_33);
lean_inc(x_3);
x_14 = x_3;
x_15 = x_44;
goto block_28;
}
else
{
lean_object* x_88; uint8_t x_89; lean_object* x_90; uint8_t x_91; 
x_88 = l_Lean_Expr_fvarId_x21(x_45);
lean_dec(x_45);
x_89 = lean_name_eq(x_88, x_1);
lean_dec(x_88);
lean_inc(x_2);
x_90 = l_Lean_MetavarContext_exprDependsOn(x_2, x_46, x_1);
x_91 = lean_unbox(x_90);
lean_dec(x_90);
if (x_91 == 0)
{
if (x_89 == 0)
{
lean_free_object(x_39);
lean_free_object(x_31);
lean_dec(x_33);
lean_inc(x_3);
x_14 = x_3;
x_15 = x_44;
goto block_28;
}
else
{
lean_object* x_92; uint8_t x_93; lean_object* x_94; 
x_92 = l_Lean_LocalDecl_fvarId(x_33);
lean_dec(x_33);
x_93 = 0;
x_94 = lean_box(x_93);
lean_ctor_set(x_39, 1, x_94);
lean_ctor_set(x_39, 0, x_92);
lean_ctor_set(x_31, 0, x_39);
x_14 = x_31;
x_15 = x_44;
goto block_28;
}
}
else
{
lean_free_object(x_39);
lean_free_object(x_31);
lean_dec(x_33);
lean_inc(x_3);
x_14 = x_3;
x_15 = x_44;
goto block_28;
}
}
}
else
{
uint8_t x_95; 
lean_free_object(x_39);
lean_free_object(x_31);
x_95 = 0;
x_48 = x_95;
goto block_64;
}
}
}
block_64:
{
if (x_48 == 0)
{
uint8_t x_49; 
x_49 = l_Lean_Expr_isFVar(x_45);
if (x_49 == 0)
{
lean_dec(x_47);
lean_dec(x_46);
lean_dec(x_45);
lean_dec(x_40);
lean_dec(x_33);
lean_inc(x_3);
x_14 = x_3;
x_15 = x_44;
goto block_28;
}
else
{
lean_object* x_50; uint8_t x_51; lean_object* x_52; uint8_t x_53; 
x_50 = l_Lean_Expr_fvarId_x21(x_45);
lean_dec(x_45);
x_51 = lean_name_eq(x_50, x_1);
lean_dec(x_50);
lean_inc(x_2);
x_52 = l_Lean_MetavarContext_exprDependsOn(x_2, x_46, x_1);
x_53 = lean_unbox(x_52);
lean_dec(x_52);
if (x_53 == 0)
{
if (x_51 == 0)
{
lean_dec(x_47);
lean_dec(x_40);
lean_dec(x_33);
lean_inc(x_3);
x_14 = x_3;
x_15 = x_44;
goto block_28;
}
else
{
lean_object* x_54; uint8_t x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_54 = l_Lean_LocalDecl_fvarId(x_33);
lean_dec(x_33);
x_55 = 0;
x_56 = lean_box(x_55);
if (lean_is_scalar(x_47)) {
 x_57 = lean_alloc_ctor(0, 2, 0);
} else {
 x_57 = x_47;
}
lean_ctor_set(x_57, 0, x_54);
lean_ctor_set(x_57, 1, x_56);
if (lean_is_scalar(x_40)) {
 x_58 = lean_alloc_ctor(1, 1, 0);
} else {
 x_58 = x_40;
}
lean_ctor_set(x_58, 0, x_57);
x_14 = x_58;
x_15 = x_44;
goto block_28;
}
}
else
{
lean_dec(x_47);
lean_dec(x_40);
lean_dec(x_33);
lean_inc(x_3);
x_14 = x_3;
x_15 = x_44;
goto block_28;
}
}
}
else
{
lean_object* x_59; uint8_t x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
lean_dec(x_46);
lean_dec(x_45);
x_59 = l_Lean_LocalDecl_fvarId(x_33);
lean_dec(x_33);
x_60 = 1;
x_61 = lean_box(x_60);
if (lean_is_scalar(x_47)) {
 x_62 = lean_alloc_ctor(0, 2, 0);
} else {
 x_62 = x_47;
}
lean_ctor_set(x_62, 0, x_59);
lean_ctor_set(x_62, 1, x_61);
if (lean_is_scalar(x_40)) {
 x_63 = lean_alloc_ctor(1, 1, 0);
} else {
 x_63 = x_40;
}
lean_ctor_set(x_63, 0, x_62);
x_14 = x_63;
x_15 = x_44;
goto block_28;
}
}
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; uint8_t x_101; uint8_t x_118; 
x_96 = lean_ctor_get(x_39, 1);
lean_inc(x_96);
lean_dec(x_39);
x_97 = lean_ctor_get(x_36, 1);
lean_inc(x_97);
lean_dec(x_36);
x_98 = lean_ctor_get(x_96, 0);
lean_inc(x_98);
x_99 = lean_ctor_get(x_96, 1);
lean_inc(x_99);
if (lean_is_exclusive(x_96)) {
 lean_ctor_release(x_96, 0);
 lean_ctor_release(x_96, 1);
 x_100 = x_96;
} else {
 lean_dec_ref(x_96);
 x_100 = lean_box(0);
}
x_118 = l_Lean_Expr_isFVar(x_99);
if (x_118 == 0)
{
uint8_t x_119; 
lean_dec(x_100);
lean_dec(x_40);
x_119 = l_Lean_Expr_isFVar(x_98);
if (x_119 == 0)
{
lean_dec(x_99);
lean_dec(x_98);
lean_free_object(x_31);
lean_dec(x_33);
lean_inc(x_3);
x_14 = x_3;
x_15 = x_97;
goto block_28;
}
else
{
lean_object* x_120; uint8_t x_121; lean_object* x_122; uint8_t x_123; 
x_120 = l_Lean_Expr_fvarId_x21(x_98);
lean_dec(x_98);
x_121 = lean_name_eq(x_120, x_1);
lean_dec(x_120);
lean_inc(x_2);
x_122 = l_Lean_MetavarContext_exprDependsOn(x_2, x_99, x_1);
x_123 = lean_unbox(x_122);
lean_dec(x_122);
if (x_123 == 0)
{
if (x_121 == 0)
{
lean_free_object(x_31);
lean_dec(x_33);
lean_inc(x_3);
x_14 = x_3;
x_15 = x_97;
goto block_28;
}
else
{
lean_object* x_124; uint8_t x_125; lean_object* x_126; lean_object* x_127; 
x_124 = l_Lean_LocalDecl_fvarId(x_33);
lean_dec(x_33);
x_125 = 0;
x_126 = lean_box(x_125);
x_127 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_127, 0, x_124);
lean_ctor_set(x_127, 1, x_126);
lean_ctor_set(x_31, 0, x_127);
x_14 = x_31;
x_15 = x_97;
goto block_28;
}
}
else
{
lean_free_object(x_31);
lean_dec(x_33);
lean_inc(x_3);
x_14 = x_3;
x_15 = x_97;
goto block_28;
}
}
}
else
{
lean_object* x_128; uint8_t x_129; lean_object* x_130; uint8_t x_131; 
x_128 = l_Lean_Expr_fvarId_x21(x_99);
x_129 = lean_name_eq(x_128, x_1);
lean_dec(x_128);
lean_inc(x_98);
lean_inc(x_2);
x_130 = l_Lean_MetavarContext_exprDependsOn(x_2, x_98, x_1);
x_131 = lean_unbox(x_130);
lean_dec(x_130);
if (x_131 == 0)
{
if (x_129 == 0)
{
uint8_t x_132; 
lean_dec(x_100);
lean_dec(x_40);
x_132 = l_Lean_Expr_isFVar(x_98);
if (x_132 == 0)
{
lean_dec(x_99);
lean_dec(x_98);
lean_free_object(x_31);
lean_dec(x_33);
lean_inc(x_3);
x_14 = x_3;
x_15 = x_97;
goto block_28;
}
else
{
lean_object* x_133; uint8_t x_134; lean_object* x_135; uint8_t x_136; 
x_133 = l_Lean_Expr_fvarId_x21(x_98);
lean_dec(x_98);
x_134 = lean_name_eq(x_133, x_1);
lean_dec(x_133);
lean_inc(x_2);
x_135 = l_Lean_MetavarContext_exprDependsOn(x_2, x_99, x_1);
x_136 = lean_unbox(x_135);
lean_dec(x_135);
if (x_136 == 0)
{
if (x_134 == 0)
{
lean_free_object(x_31);
lean_dec(x_33);
lean_inc(x_3);
x_14 = x_3;
x_15 = x_97;
goto block_28;
}
else
{
lean_object* x_137; uint8_t x_138; lean_object* x_139; lean_object* x_140; 
x_137 = l_Lean_LocalDecl_fvarId(x_33);
lean_dec(x_33);
x_138 = 0;
x_139 = lean_box(x_138);
x_140 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_140, 0, x_137);
lean_ctor_set(x_140, 1, x_139);
lean_ctor_set(x_31, 0, x_140);
x_14 = x_31;
x_15 = x_97;
goto block_28;
}
}
else
{
lean_free_object(x_31);
lean_dec(x_33);
lean_inc(x_3);
x_14 = x_3;
x_15 = x_97;
goto block_28;
}
}
}
else
{
uint8_t x_141; 
lean_free_object(x_31);
x_141 = 1;
x_101 = x_141;
goto block_117;
}
}
else
{
if (x_129 == 0)
{
uint8_t x_142; 
lean_dec(x_100);
lean_dec(x_40);
x_142 = l_Lean_Expr_isFVar(x_98);
if (x_142 == 0)
{
lean_dec(x_99);
lean_dec(x_98);
lean_free_object(x_31);
lean_dec(x_33);
lean_inc(x_3);
x_14 = x_3;
x_15 = x_97;
goto block_28;
}
else
{
lean_object* x_143; uint8_t x_144; lean_object* x_145; uint8_t x_146; 
x_143 = l_Lean_Expr_fvarId_x21(x_98);
lean_dec(x_98);
x_144 = lean_name_eq(x_143, x_1);
lean_dec(x_143);
lean_inc(x_2);
x_145 = l_Lean_MetavarContext_exprDependsOn(x_2, x_99, x_1);
x_146 = lean_unbox(x_145);
lean_dec(x_145);
if (x_146 == 0)
{
if (x_144 == 0)
{
lean_free_object(x_31);
lean_dec(x_33);
lean_inc(x_3);
x_14 = x_3;
x_15 = x_97;
goto block_28;
}
else
{
lean_object* x_147; uint8_t x_148; lean_object* x_149; lean_object* x_150; 
x_147 = l_Lean_LocalDecl_fvarId(x_33);
lean_dec(x_33);
x_148 = 0;
x_149 = lean_box(x_148);
x_150 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_150, 0, x_147);
lean_ctor_set(x_150, 1, x_149);
lean_ctor_set(x_31, 0, x_150);
x_14 = x_31;
x_15 = x_97;
goto block_28;
}
}
else
{
lean_free_object(x_31);
lean_dec(x_33);
lean_inc(x_3);
x_14 = x_3;
x_15 = x_97;
goto block_28;
}
}
}
else
{
uint8_t x_151; 
lean_free_object(x_31);
x_151 = 0;
x_101 = x_151;
goto block_117;
}
}
}
block_117:
{
if (x_101 == 0)
{
uint8_t x_102; 
x_102 = l_Lean_Expr_isFVar(x_98);
if (x_102 == 0)
{
lean_dec(x_100);
lean_dec(x_99);
lean_dec(x_98);
lean_dec(x_40);
lean_dec(x_33);
lean_inc(x_3);
x_14 = x_3;
x_15 = x_97;
goto block_28;
}
else
{
lean_object* x_103; uint8_t x_104; lean_object* x_105; uint8_t x_106; 
x_103 = l_Lean_Expr_fvarId_x21(x_98);
lean_dec(x_98);
x_104 = lean_name_eq(x_103, x_1);
lean_dec(x_103);
lean_inc(x_2);
x_105 = l_Lean_MetavarContext_exprDependsOn(x_2, x_99, x_1);
x_106 = lean_unbox(x_105);
lean_dec(x_105);
if (x_106 == 0)
{
if (x_104 == 0)
{
lean_dec(x_100);
lean_dec(x_40);
lean_dec(x_33);
lean_inc(x_3);
x_14 = x_3;
x_15 = x_97;
goto block_28;
}
else
{
lean_object* x_107; uint8_t x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_107 = l_Lean_LocalDecl_fvarId(x_33);
lean_dec(x_33);
x_108 = 0;
x_109 = lean_box(x_108);
if (lean_is_scalar(x_100)) {
 x_110 = lean_alloc_ctor(0, 2, 0);
} else {
 x_110 = x_100;
}
lean_ctor_set(x_110, 0, x_107);
lean_ctor_set(x_110, 1, x_109);
if (lean_is_scalar(x_40)) {
 x_111 = lean_alloc_ctor(1, 1, 0);
} else {
 x_111 = x_40;
}
lean_ctor_set(x_111, 0, x_110);
x_14 = x_111;
x_15 = x_97;
goto block_28;
}
}
else
{
lean_dec(x_100);
lean_dec(x_40);
lean_dec(x_33);
lean_inc(x_3);
x_14 = x_3;
x_15 = x_97;
goto block_28;
}
}
}
else
{
lean_object* x_112; uint8_t x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; 
lean_dec(x_99);
lean_dec(x_98);
x_112 = l_Lean_LocalDecl_fvarId(x_33);
lean_dec(x_33);
x_113 = 1;
x_114 = lean_box(x_113);
if (lean_is_scalar(x_100)) {
 x_115 = lean_alloc_ctor(0, 2, 0);
} else {
 x_115 = x_100;
}
lean_ctor_set(x_115, 0, x_112);
lean_ctor_set(x_115, 1, x_114);
if (lean_is_scalar(x_40)) {
 x_116 = lean_alloc_ctor(1, 1, 0);
} else {
 x_116 = x_40;
}
lean_ctor_set(x_116, 0, x_115);
x_14 = x_116;
x_15 = x_97;
goto block_28;
}
}
}
}
}
else
{
uint8_t x_152; 
lean_free_object(x_31);
lean_dec(x_33);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_152 = !lean_is_exclusive(x_36);
if (x_152 == 0)
{
return x_36;
}
else
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; 
x_153 = lean_ctor_get(x_36, 0);
x_154 = lean_ctor_get(x_36, 1);
lean_inc(x_154);
lean_inc(x_153);
lean_dec(x_36);
x_155 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_155, 0, x_153);
lean_ctor_set(x_155, 1, x_154);
return x_155;
}
}
}
else
{
lean_free_object(x_31);
lean_dec(x_33);
lean_inc(x_3);
x_14 = x_3;
x_15 = x_13;
goto block_28;
}
}
else
{
lean_object* x_156; uint8_t x_157; 
x_156 = lean_ctor_get(x_31, 0);
lean_inc(x_156);
lean_dec(x_31);
x_157 = l_Lean_LocalDecl_isAuxDecl(x_156);
if (x_157 == 0)
{
lean_object* x_158; lean_object* x_159; 
x_158 = l_Lean_LocalDecl_type(x_156);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_159 = l_Lean_Meta_matchEq_x3f(x_158, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_159) == 0)
{
lean_object* x_160; 
x_160 = lean_ctor_get(x_159, 0);
lean_inc(x_160);
if (lean_obj_tag(x_160) == 0)
{
lean_object* x_161; 
lean_dec(x_156);
x_161 = lean_ctor_get(x_159, 1);
lean_inc(x_161);
lean_dec(x_159);
lean_inc(x_3);
x_14 = x_3;
x_15 = x_161;
goto block_28;
}
else
{
lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; uint8_t x_170; uint8_t x_187; 
x_162 = lean_ctor_get(x_160, 0);
lean_inc(x_162);
if (lean_is_exclusive(x_160)) {
 lean_ctor_release(x_160, 0);
 x_163 = x_160;
} else {
 lean_dec_ref(x_160);
 x_163 = lean_box(0);
}
x_164 = lean_ctor_get(x_162, 1);
lean_inc(x_164);
if (lean_is_exclusive(x_162)) {
 lean_ctor_release(x_162, 0);
 lean_ctor_release(x_162, 1);
 x_165 = x_162;
} else {
 lean_dec_ref(x_162);
 x_165 = lean_box(0);
}
x_166 = lean_ctor_get(x_159, 1);
lean_inc(x_166);
lean_dec(x_159);
x_167 = lean_ctor_get(x_164, 0);
lean_inc(x_167);
x_168 = lean_ctor_get(x_164, 1);
lean_inc(x_168);
if (lean_is_exclusive(x_164)) {
 lean_ctor_release(x_164, 0);
 lean_ctor_release(x_164, 1);
 x_169 = x_164;
} else {
 lean_dec_ref(x_164);
 x_169 = lean_box(0);
}
x_187 = l_Lean_Expr_isFVar(x_168);
if (x_187 == 0)
{
uint8_t x_188; 
lean_dec(x_169);
lean_dec(x_163);
x_188 = l_Lean_Expr_isFVar(x_167);
if (x_188 == 0)
{
lean_dec(x_168);
lean_dec(x_167);
lean_dec(x_165);
lean_dec(x_156);
lean_inc(x_3);
x_14 = x_3;
x_15 = x_166;
goto block_28;
}
else
{
lean_object* x_189; uint8_t x_190; lean_object* x_191; uint8_t x_192; 
x_189 = l_Lean_Expr_fvarId_x21(x_167);
lean_dec(x_167);
x_190 = lean_name_eq(x_189, x_1);
lean_dec(x_189);
lean_inc(x_2);
x_191 = l_Lean_MetavarContext_exprDependsOn(x_2, x_168, x_1);
x_192 = lean_unbox(x_191);
lean_dec(x_191);
if (x_192 == 0)
{
if (x_190 == 0)
{
lean_dec(x_165);
lean_dec(x_156);
lean_inc(x_3);
x_14 = x_3;
x_15 = x_166;
goto block_28;
}
else
{
lean_object* x_193; uint8_t x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; 
x_193 = l_Lean_LocalDecl_fvarId(x_156);
lean_dec(x_156);
x_194 = 0;
x_195 = lean_box(x_194);
if (lean_is_scalar(x_165)) {
 x_196 = lean_alloc_ctor(0, 2, 0);
} else {
 x_196 = x_165;
}
lean_ctor_set(x_196, 0, x_193);
lean_ctor_set(x_196, 1, x_195);
x_197 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_197, 0, x_196);
x_14 = x_197;
x_15 = x_166;
goto block_28;
}
}
else
{
lean_dec(x_165);
lean_dec(x_156);
lean_inc(x_3);
x_14 = x_3;
x_15 = x_166;
goto block_28;
}
}
}
else
{
lean_object* x_198; uint8_t x_199; lean_object* x_200; uint8_t x_201; 
x_198 = l_Lean_Expr_fvarId_x21(x_168);
x_199 = lean_name_eq(x_198, x_1);
lean_dec(x_198);
lean_inc(x_167);
lean_inc(x_2);
x_200 = l_Lean_MetavarContext_exprDependsOn(x_2, x_167, x_1);
x_201 = lean_unbox(x_200);
lean_dec(x_200);
if (x_201 == 0)
{
if (x_199 == 0)
{
uint8_t x_202; 
lean_dec(x_169);
lean_dec(x_163);
x_202 = l_Lean_Expr_isFVar(x_167);
if (x_202 == 0)
{
lean_dec(x_168);
lean_dec(x_167);
lean_dec(x_165);
lean_dec(x_156);
lean_inc(x_3);
x_14 = x_3;
x_15 = x_166;
goto block_28;
}
else
{
lean_object* x_203; uint8_t x_204; lean_object* x_205; uint8_t x_206; 
x_203 = l_Lean_Expr_fvarId_x21(x_167);
lean_dec(x_167);
x_204 = lean_name_eq(x_203, x_1);
lean_dec(x_203);
lean_inc(x_2);
x_205 = l_Lean_MetavarContext_exprDependsOn(x_2, x_168, x_1);
x_206 = lean_unbox(x_205);
lean_dec(x_205);
if (x_206 == 0)
{
if (x_204 == 0)
{
lean_dec(x_165);
lean_dec(x_156);
lean_inc(x_3);
x_14 = x_3;
x_15 = x_166;
goto block_28;
}
else
{
lean_object* x_207; uint8_t x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; 
x_207 = l_Lean_LocalDecl_fvarId(x_156);
lean_dec(x_156);
x_208 = 0;
x_209 = lean_box(x_208);
if (lean_is_scalar(x_165)) {
 x_210 = lean_alloc_ctor(0, 2, 0);
} else {
 x_210 = x_165;
}
lean_ctor_set(x_210, 0, x_207);
lean_ctor_set(x_210, 1, x_209);
x_211 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_211, 0, x_210);
x_14 = x_211;
x_15 = x_166;
goto block_28;
}
}
else
{
lean_dec(x_165);
lean_dec(x_156);
lean_inc(x_3);
x_14 = x_3;
x_15 = x_166;
goto block_28;
}
}
}
else
{
uint8_t x_212; 
lean_dec(x_165);
x_212 = 1;
x_170 = x_212;
goto block_186;
}
}
else
{
if (x_199 == 0)
{
uint8_t x_213; 
lean_dec(x_169);
lean_dec(x_163);
x_213 = l_Lean_Expr_isFVar(x_167);
if (x_213 == 0)
{
lean_dec(x_168);
lean_dec(x_167);
lean_dec(x_165);
lean_dec(x_156);
lean_inc(x_3);
x_14 = x_3;
x_15 = x_166;
goto block_28;
}
else
{
lean_object* x_214; uint8_t x_215; lean_object* x_216; uint8_t x_217; 
x_214 = l_Lean_Expr_fvarId_x21(x_167);
lean_dec(x_167);
x_215 = lean_name_eq(x_214, x_1);
lean_dec(x_214);
lean_inc(x_2);
x_216 = l_Lean_MetavarContext_exprDependsOn(x_2, x_168, x_1);
x_217 = lean_unbox(x_216);
lean_dec(x_216);
if (x_217 == 0)
{
if (x_215 == 0)
{
lean_dec(x_165);
lean_dec(x_156);
lean_inc(x_3);
x_14 = x_3;
x_15 = x_166;
goto block_28;
}
else
{
lean_object* x_218; uint8_t x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; 
x_218 = l_Lean_LocalDecl_fvarId(x_156);
lean_dec(x_156);
x_219 = 0;
x_220 = lean_box(x_219);
if (lean_is_scalar(x_165)) {
 x_221 = lean_alloc_ctor(0, 2, 0);
} else {
 x_221 = x_165;
}
lean_ctor_set(x_221, 0, x_218);
lean_ctor_set(x_221, 1, x_220);
x_222 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_222, 0, x_221);
x_14 = x_222;
x_15 = x_166;
goto block_28;
}
}
else
{
lean_dec(x_165);
lean_dec(x_156);
lean_inc(x_3);
x_14 = x_3;
x_15 = x_166;
goto block_28;
}
}
}
else
{
uint8_t x_223; 
lean_dec(x_165);
x_223 = 0;
x_170 = x_223;
goto block_186;
}
}
}
block_186:
{
if (x_170 == 0)
{
uint8_t x_171; 
x_171 = l_Lean_Expr_isFVar(x_167);
if (x_171 == 0)
{
lean_dec(x_169);
lean_dec(x_168);
lean_dec(x_167);
lean_dec(x_163);
lean_dec(x_156);
lean_inc(x_3);
x_14 = x_3;
x_15 = x_166;
goto block_28;
}
else
{
lean_object* x_172; uint8_t x_173; lean_object* x_174; uint8_t x_175; 
x_172 = l_Lean_Expr_fvarId_x21(x_167);
lean_dec(x_167);
x_173 = lean_name_eq(x_172, x_1);
lean_dec(x_172);
lean_inc(x_2);
x_174 = l_Lean_MetavarContext_exprDependsOn(x_2, x_168, x_1);
x_175 = lean_unbox(x_174);
lean_dec(x_174);
if (x_175 == 0)
{
if (x_173 == 0)
{
lean_dec(x_169);
lean_dec(x_163);
lean_dec(x_156);
lean_inc(x_3);
x_14 = x_3;
x_15 = x_166;
goto block_28;
}
else
{
lean_object* x_176; uint8_t x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; 
x_176 = l_Lean_LocalDecl_fvarId(x_156);
lean_dec(x_156);
x_177 = 0;
x_178 = lean_box(x_177);
if (lean_is_scalar(x_169)) {
 x_179 = lean_alloc_ctor(0, 2, 0);
} else {
 x_179 = x_169;
}
lean_ctor_set(x_179, 0, x_176);
lean_ctor_set(x_179, 1, x_178);
if (lean_is_scalar(x_163)) {
 x_180 = lean_alloc_ctor(1, 1, 0);
} else {
 x_180 = x_163;
}
lean_ctor_set(x_180, 0, x_179);
x_14 = x_180;
x_15 = x_166;
goto block_28;
}
}
else
{
lean_dec(x_169);
lean_dec(x_163);
lean_dec(x_156);
lean_inc(x_3);
x_14 = x_3;
x_15 = x_166;
goto block_28;
}
}
}
else
{
lean_object* x_181; uint8_t x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; 
lean_dec(x_168);
lean_dec(x_167);
x_181 = l_Lean_LocalDecl_fvarId(x_156);
lean_dec(x_156);
x_182 = 1;
x_183 = lean_box(x_182);
if (lean_is_scalar(x_169)) {
 x_184 = lean_alloc_ctor(0, 2, 0);
} else {
 x_184 = x_169;
}
lean_ctor_set(x_184, 0, x_181);
lean_ctor_set(x_184, 1, x_183);
if (lean_is_scalar(x_163)) {
 x_185 = lean_alloc_ctor(1, 1, 0);
} else {
 x_185 = x_163;
}
lean_ctor_set(x_185, 0, x_184);
x_14 = x_185;
x_15 = x_166;
goto block_28;
}
}
}
}
else
{
lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; 
lean_dec(x_156);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_224 = lean_ctor_get(x_159, 0);
lean_inc(x_224);
x_225 = lean_ctor_get(x_159, 1);
lean_inc(x_225);
if (lean_is_exclusive(x_159)) {
 lean_ctor_release(x_159, 0);
 lean_ctor_release(x_159, 1);
 x_226 = x_159;
} else {
 lean_dec_ref(x_159);
 x_226 = lean_box(0);
}
if (lean_is_scalar(x_226)) {
 x_227 = lean_alloc_ctor(1, 2, 0);
} else {
 x_227 = x_226;
}
lean_ctor_set(x_227, 0, x_224);
lean_ctor_set(x_227, 1, x_225);
return x_227;
}
}
else
{
lean_dec(x_156);
lean_inc(x_3);
x_14 = x_3;
x_15 = x_13;
goto block_28;
}
}
}
}
block_28:
{
if (lean_obj_tag(x_14) == 0)
{
size_t x_16; size_t x_17; 
x_16 = 1;
x_17 = x_7 + x_16;
lean_inc(x_4);
{
size_t _tmp_6 = x_17;
lean_object* _tmp_7 = x_4;
lean_object* _tmp_12 = x_15;
x_7 = _tmp_6;
x_8 = _tmp_7;
x_13 = _tmp_12;
}
goto _start;
}
else
{
uint8_t x_19; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_19 = !lean_is_exclusive(x_14);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_box(0);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_14);
lean_ctor_set(x_21, 1, x_20);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_15);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_23 = lean_ctor_get(x_14, 0);
lean_inc(x_23);
lean_dec(x_14);
x_24 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_24, 0, x_23);
x_25 = lean_box(0);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_15);
return x_27;
}
}
}
}
}
lean_object* l_Std_PersistentArray_findSomeMAux___at_Lean_Meta_subst___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; size_t x_12; size_t x_13; lean_object* x_14; lean_object* x_15; 
x_9 = lean_ctor_get(x_3, 0);
x_10 = lean_box(0);
x_11 = lean_array_get_size(x_9);
x_12 = lean_usize_of_nat(x_11);
lean_dec(x_11);
x_13 = 0;
x_14 = l_Array_findSomeM_x3f___rarg___closed__1;
x_15 = l_Array_forInUnsafe_loop___at_Lean_Meta_subst___spec__4(x_1, x_2, x_14, x_9, x_12, x_13, x_14, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
lean_dec(x_16);
if (lean_obj_tag(x_17) == 0)
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_15);
if (x_18 == 0)
{
lean_object* x_19; 
x_19 = lean_ctor_get(x_15, 0);
lean_dec(x_19);
lean_ctor_set(x_15, 0, x_10);
return x_15;
}
else
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_15, 1);
lean_inc(x_20);
lean_dec(x_15);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_10);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
else
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_15);
if (x_22 == 0)
{
lean_object* x_23; uint8_t x_24; 
x_23 = lean_ctor_get(x_15, 0);
lean_dec(x_23);
x_24 = !lean_is_exclusive(x_17);
if (x_24 == 0)
{
lean_ctor_set(x_15, 0, x_17);
return x_15;
}
else
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_17, 0);
lean_inc(x_25);
lean_dec(x_17);
x_26 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_15, 0, x_26);
return x_15;
}
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_27 = lean_ctor_get(x_15, 1);
lean_inc(x_27);
lean_dec(x_15);
x_28 = lean_ctor_get(x_17, 0);
lean_inc(x_28);
if (lean_is_exclusive(x_17)) {
 lean_ctor_release(x_17, 0);
 x_29 = x_17;
} else {
 lean_dec_ref(x_17);
 x_29 = lean_box(0);
}
if (lean_is_scalar(x_29)) {
 x_30 = lean_alloc_ctor(1, 1, 0);
} else {
 x_30 = x_29;
}
lean_ctor_set(x_30, 0, x_28);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_27);
return x_31;
}
}
}
else
{
uint8_t x_32; 
x_32 = !lean_is_exclusive(x_15);
if (x_32 == 0)
{
return x_15;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_15, 0);
x_34 = lean_ctor_get(x_15, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_15);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; size_t x_39; size_t x_40; lean_object* x_41; lean_object* x_42; 
x_36 = lean_ctor_get(x_3, 0);
x_37 = lean_box(0);
x_38 = lean_array_get_size(x_36);
x_39 = lean_usize_of_nat(x_38);
lean_dec(x_38);
x_40 = 0;
x_41 = l_Array_findSomeM_x3f___rarg___closed__1;
x_42 = l_Array_forInUnsafe_loop___at_Lean_Meta_subst___spec__5(x_1, x_2, x_37, x_41, x_36, x_39, x_40, x_41, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
lean_dec(x_43);
if (lean_obj_tag(x_44) == 0)
{
uint8_t x_45; 
x_45 = !lean_is_exclusive(x_42);
if (x_45 == 0)
{
lean_object* x_46; 
x_46 = lean_ctor_get(x_42, 0);
lean_dec(x_46);
lean_ctor_set(x_42, 0, x_37);
return x_42;
}
else
{
lean_object* x_47; lean_object* x_48; 
x_47 = lean_ctor_get(x_42, 1);
lean_inc(x_47);
lean_dec(x_42);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_37);
lean_ctor_set(x_48, 1, x_47);
return x_48;
}
}
else
{
uint8_t x_49; 
x_49 = !lean_is_exclusive(x_42);
if (x_49 == 0)
{
lean_object* x_50; uint8_t x_51; 
x_50 = lean_ctor_get(x_42, 0);
lean_dec(x_50);
x_51 = !lean_is_exclusive(x_44);
if (x_51 == 0)
{
lean_ctor_set(x_42, 0, x_44);
return x_42;
}
else
{
lean_object* x_52; lean_object* x_53; 
x_52 = lean_ctor_get(x_44, 0);
lean_inc(x_52);
lean_dec(x_44);
x_53 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_42, 0, x_53);
return x_42;
}
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_54 = lean_ctor_get(x_42, 1);
lean_inc(x_54);
lean_dec(x_42);
x_55 = lean_ctor_get(x_44, 0);
lean_inc(x_55);
if (lean_is_exclusive(x_44)) {
 lean_ctor_release(x_44, 0);
 x_56 = x_44;
} else {
 lean_dec_ref(x_44);
 x_56 = lean_box(0);
}
if (lean_is_scalar(x_56)) {
 x_57 = lean_alloc_ctor(1, 1, 0);
} else {
 x_57 = x_56;
}
lean_ctor_set(x_57, 0, x_55);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_54);
return x_58;
}
}
}
else
{
uint8_t x_59; 
x_59 = !lean_is_exclusive(x_42);
if (x_59 == 0)
{
return x_42;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_60 = lean_ctor_get(x_42, 0);
x_61 = lean_ctor_get(x_42, 1);
lean_inc(x_61);
lean_inc(x_60);
lean_dec(x_42);
x_62 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_62, 0, x_60);
lean_ctor_set(x_62, 1, x_61);
return x_62;
}
}
}
}
}
lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_subst___spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, size_t x_6, size_t x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_15; uint8_t x_29; 
x_29 = x_7 < x_6;
if (x_29 == 0)
{
lean_object* x_30; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_8);
lean_ctor_set(x_30, 1, x_13);
return x_30;
}
else
{
lean_object* x_31; 
lean_dec(x_8);
x_31 = lean_array_uget(x_5, x_7);
if (lean_obj_tag(x_31) == 0)
{
lean_inc(x_3);
x_14 = x_3;
x_15 = x_13;
goto block_28;
}
else
{
uint8_t x_32; 
x_32 = !lean_is_exclusive(x_31);
if (x_32 == 0)
{
lean_object* x_33; uint8_t x_34; 
x_33 = lean_ctor_get(x_31, 0);
x_34 = l_Lean_LocalDecl_isAuxDecl(x_33);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; 
x_35 = l_Lean_LocalDecl_type(x_33);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_36 = l_Lean_Meta_matchEq_x3f(x_35, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; 
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; 
lean_free_object(x_31);
lean_dec(x_33);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
lean_dec(x_36);
lean_inc(x_3);
x_14 = x_3;
x_15 = x_38;
goto block_28;
}
else
{
lean_object* x_39; lean_object* x_40; uint8_t x_41; 
x_39 = lean_ctor_get(x_37, 0);
lean_inc(x_39);
if (lean_is_exclusive(x_37)) {
 lean_ctor_release(x_37, 0);
 x_40 = x_37;
} else {
 lean_dec_ref(x_37);
 x_40 = lean_box(0);
}
x_41 = !lean_is_exclusive(x_39);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; uint8_t x_65; 
x_42 = lean_ctor_get(x_39, 1);
x_43 = lean_ctor_get(x_39, 0);
lean_dec(x_43);
x_44 = lean_ctor_get(x_36, 1);
lean_inc(x_44);
lean_dec(x_36);
x_45 = lean_ctor_get(x_42, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_42, 1);
lean_inc(x_46);
if (lean_is_exclusive(x_42)) {
 lean_ctor_release(x_42, 0);
 lean_ctor_release(x_42, 1);
 x_47 = x_42;
} else {
 lean_dec_ref(x_42);
 x_47 = lean_box(0);
}
x_65 = l_Lean_Expr_isFVar(x_46);
if (x_65 == 0)
{
uint8_t x_66; 
lean_dec(x_47);
lean_dec(x_40);
x_66 = l_Lean_Expr_isFVar(x_45);
if (x_66 == 0)
{
lean_dec(x_46);
lean_dec(x_45);
lean_free_object(x_39);
lean_free_object(x_31);
lean_dec(x_33);
lean_inc(x_3);
x_14 = x_3;
x_15 = x_44;
goto block_28;
}
else
{
lean_object* x_67; uint8_t x_68; lean_object* x_69; uint8_t x_70; 
x_67 = l_Lean_Expr_fvarId_x21(x_45);
lean_dec(x_45);
x_68 = lean_name_eq(x_67, x_1);
lean_dec(x_67);
lean_inc(x_2);
x_69 = l_Lean_MetavarContext_exprDependsOn(x_2, x_46, x_1);
x_70 = lean_unbox(x_69);
lean_dec(x_69);
if (x_70 == 0)
{
if (x_68 == 0)
{
lean_free_object(x_39);
lean_free_object(x_31);
lean_dec(x_33);
lean_inc(x_3);
x_14 = x_3;
x_15 = x_44;
goto block_28;
}
else
{
lean_object* x_71; uint8_t x_72; lean_object* x_73; 
x_71 = l_Lean_LocalDecl_fvarId(x_33);
lean_dec(x_33);
x_72 = 0;
x_73 = lean_box(x_72);
lean_ctor_set(x_39, 1, x_73);
lean_ctor_set(x_39, 0, x_71);
lean_ctor_set(x_31, 0, x_39);
x_14 = x_31;
x_15 = x_44;
goto block_28;
}
}
else
{
lean_free_object(x_39);
lean_free_object(x_31);
lean_dec(x_33);
lean_inc(x_3);
x_14 = x_3;
x_15 = x_44;
goto block_28;
}
}
}
else
{
lean_object* x_74; uint8_t x_75; lean_object* x_76; uint8_t x_77; 
x_74 = l_Lean_Expr_fvarId_x21(x_46);
x_75 = lean_name_eq(x_74, x_1);
lean_dec(x_74);
lean_inc(x_45);
lean_inc(x_2);
x_76 = l_Lean_MetavarContext_exprDependsOn(x_2, x_45, x_1);
x_77 = lean_unbox(x_76);
lean_dec(x_76);
if (x_77 == 0)
{
if (x_75 == 0)
{
uint8_t x_78; 
lean_dec(x_47);
lean_dec(x_40);
x_78 = l_Lean_Expr_isFVar(x_45);
if (x_78 == 0)
{
lean_dec(x_46);
lean_dec(x_45);
lean_free_object(x_39);
lean_free_object(x_31);
lean_dec(x_33);
lean_inc(x_3);
x_14 = x_3;
x_15 = x_44;
goto block_28;
}
else
{
lean_object* x_79; uint8_t x_80; lean_object* x_81; uint8_t x_82; 
x_79 = l_Lean_Expr_fvarId_x21(x_45);
lean_dec(x_45);
x_80 = lean_name_eq(x_79, x_1);
lean_dec(x_79);
lean_inc(x_2);
x_81 = l_Lean_MetavarContext_exprDependsOn(x_2, x_46, x_1);
x_82 = lean_unbox(x_81);
lean_dec(x_81);
if (x_82 == 0)
{
if (x_80 == 0)
{
lean_free_object(x_39);
lean_free_object(x_31);
lean_dec(x_33);
lean_inc(x_3);
x_14 = x_3;
x_15 = x_44;
goto block_28;
}
else
{
lean_object* x_83; uint8_t x_84; lean_object* x_85; 
x_83 = l_Lean_LocalDecl_fvarId(x_33);
lean_dec(x_33);
x_84 = 0;
x_85 = lean_box(x_84);
lean_ctor_set(x_39, 1, x_85);
lean_ctor_set(x_39, 0, x_83);
lean_ctor_set(x_31, 0, x_39);
x_14 = x_31;
x_15 = x_44;
goto block_28;
}
}
else
{
lean_free_object(x_39);
lean_free_object(x_31);
lean_dec(x_33);
lean_inc(x_3);
x_14 = x_3;
x_15 = x_44;
goto block_28;
}
}
}
else
{
uint8_t x_86; 
lean_free_object(x_39);
lean_free_object(x_31);
x_86 = 1;
x_48 = x_86;
goto block_64;
}
}
else
{
if (x_75 == 0)
{
uint8_t x_87; 
lean_dec(x_47);
lean_dec(x_40);
x_87 = l_Lean_Expr_isFVar(x_45);
if (x_87 == 0)
{
lean_dec(x_46);
lean_dec(x_45);
lean_free_object(x_39);
lean_free_object(x_31);
lean_dec(x_33);
lean_inc(x_3);
x_14 = x_3;
x_15 = x_44;
goto block_28;
}
else
{
lean_object* x_88; uint8_t x_89; lean_object* x_90; uint8_t x_91; 
x_88 = l_Lean_Expr_fvarId_x21(x_45);
lean_dec(x_45);
x_89 = lean_name_eq(x_88, x_1);
lean_dec(x_88);
lean_inc(x_2);
x_90 = l_Lean_MetavarContext_exprDependsOn(x_2, x_46, x_1);
x_91 = lean_unbox(x_90);
lean_dec(x_90);
if (x_91 == 0)
{
if (x_89 == 0)
{
lean_free_object(x_39);
lean_free_object(x_31);
lean_dec(x_33);
lean_inc(x_3);
x_14 = x_3;
x_15 = x_44;
goto block_28;
}
else
{
lean_object* x_92; uint8_t x_93; lean_object* x_94; 
x_92 = l_Lean_LocalDecl_fvarId(x_33);
lean_dec(x_33);
x_93 = 0;
x_94 = lean_box(x_93);
lean_ctor_set(x_39, 1, x_94);
lean_ctor_set(x_39, 0, x_92);
lean_ctor_set(x_31, 0, x_39);
x_14 = x_31;
x_15 = x_44;
goto block_28;
}
}
else
{
lean_free_object(x_39);
lean_free_object(x_31);
lean_dec(x_33);
lean_inc(x_3);
x_14 = x_3;
x_15 = x_44;
goto block_28;
}
}
}
else
{
uint8_t x_95; 
lean_free_object(x_39);
lean_free_object(x_31);
x_95 = 0;
x_48 = x_95;
goto block_64;
}
}
}
block_64:
{
if (x_48 == 0)
{
uint8_t x_49; 
x_49 = l_Lean_Expr_isFVar(x_45);
if (x_49 == 0)
{
lean_dec(x_47);
lean_dec(x_46);
lean_dec(x_45);
lean_dec(x_40);
lean_dec(x_33);
lean_inc(x_3);
x_14 = x_3;
x_15 = x_44;
goto block_28;
}
else
{
lean_object* x_50; uint8_t x_51; lean_object* x_52; uint8_t x_53; 
x_50 = l_Lean_Expr_fvarId_x21(x_45);
lean_dec(x_45);
x_51 = lean_name_eq(x_50, x_1);
lean_dec(x_50);
lean_inc(x_2);
x_52 = l_Lean_MetavarContext_exprDependsOn(x_2, x_46, x_1);
x_53 = lean_unbox(x_52);
lean_dec(x_52);
if (x_53 == 0)
{
if (x_51 == 0)
{
lean_dec(x_47);
lean_dec(x_40);
lean_dec(x_33);
lean_inc(x_3);
x_14 = x_3;
x_15 = x_44;
goto block_28;
}
else
{
lean_object* x_54; uint8_t x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_54 = l_Lean_LocalDecl_fvarId(x_33);
lean_dec(x_33);
x_55 = 0;
x_56 = lean_box(x_55);
if (lean_is_scalar(x_47)) {
 x_57 = lean_alloc_ctor(0, 2, 0);
} else {
 x_57 = x_47;
}
lean_ctor_set(x_57, 0, x_54);
lean_ctor_set(x_57, 1, x_56);
if (lean_is_scalar(x_40)) {
 x_58 = lean_alloc_ctor(1, 1, 0);
} else {
 x_58 = x_40;
}
lean_ctor_set(x_58, 0, x_57);
x_14 = x_58;
x_15 = x_44;
goto block_28;
}
}
else
{
lean_dec(x_47);
lean_dec(x_40);
lean_dec(x_33);
lean_inc(x_3);
x_14 = x_3;
x_15 = x_44;
goto block_28;
}
}
}
else
{
lean_object* x_59; uint8_t x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
lean_dec(x_46);
lean_dec(x_45);
x_59 = l_Lean_LocalDecl_fvarId(x_33);
lean_dec(x_33);
x_60 = 1;
x_61 = lean_box(x_60);
if (lean_is_scalar(x_47)) {
 x_62 = lean_alloc_ctor(0, 2, 0);
} else {
 x_62 = x_47;
}
lean_ctor_set(x_62, 0, x_59);
lean_ctor_set(x_62, 1, x_61);
if (lean_is_scalar(x_40)) {
 x_63 = lean_alloc_ctor(1, 1, 0);
} else {
 x_63 = x_40;
}
lean_ctor_set(x_63, 0, x_62);
x_14 = x_63;
x_15 = x_44;
goto block_28;
}
}
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; uint8_t x_101; uint8_t x_118; 
x_96 = lean_ctor_get(x_39, 1);
lean_inc(x_96);
lean_dec(x_39);
x_97 = lean_ctor_get(x_36, 1);
lean_inc(x_97);
lean_dec(x_36);
x_98 = lean_ctor_get(x_96, 0);
lean_inc(x_98);
x_99 = lean_ctor_get(x_96, 1);
lean_inc(x_99);
if (lean_is_exclusive(x_96)) {
 lean_ctor_release(x_96, 0);
 lean_ctor_release(x_96, 1);
 x_100 = x_96;
} else {
 lean_dec_ref(x_96);
 x_100 = lean_box(0);
}
x_118 = l_Lean_Expr_isFVar(x_99);
if (x_118 == 0)
{
uint8_t x_119; 
lean_dec(x_100);
lean_dec(x_40);
x_119 = l_Lean_Expr_isFVar(x_98);
if (x_119 == 0)
{
lean_dec(x_99);
lean_dec(x_98);
lean_free_object(x_31);
lean_dec(x_33);
lean_inc(x_3);
x_14 = x_3;
x_15 = x_97;
goto block_28;
}
else
{
lean_object* x_120; uint8_t x_121; lean_object* x_122; uint8_t x_123; 
x_120 = l_Lean_Expr_fvarId_x21(x_98);
lean_dec(x_98);
x_121 = lean_name_eq(x_120, x_1);
lean_dec(x_120);
lean_inc(x_2);
x_122 = l_Lean_MetavarContext_exprDependsOn(x_2, x_99, x_1);
x_123 = lean_unbox(x_122);
lean_dec(x_122);
if (x_123 == 0)
{
if (x_121 == 0)
{
lean_free_object(x_31);
lean_dec(x_33);
lean_inc(x_3);
x_14 = x_3;
x_15 = x_97;
goto block_28;
}
else
{
lean_object* x_124; uint8_t x_125; lean_object* x_126; lean_object* x_127; 
x_124 = l_Lean_LocalDecl_fvarId(x_33);
lean_dec(x_33);
x_125 = 0;
x_126 = lean_box(x_125);
x_127 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_127, 0, x_124);
lean_ctor_set(x_127, 1, x_126);
lean_ctor_set(x_31, 0, x_127);
x_14 = x_31;
x_15 = x_97;
goto block_28;
}
}
else
{
lean_free_object(x_31);
lean_dec(x_33);
lean_inc(x_3);
x_14 = x_3;
x_15 = x_97;
goto block_28;
}
}
}
else
{
lean_object* x_128; uint8_t x_129; lean_object* x_130; uint8_t x_131; 
x_128 = l_Lean_Expr_fvarId_x21(x_99);
x_129 = lean_name_eq(x_128, x_1);
lean_dec(x_128);
lean_inc(x_98);
lean_inc(x_2);
x_130 = l_Lean_MetavarContext_exprDependsOn(x_2, x_98, x_1);
x_131 = lean_unbox(x_130);
lean_dec(x_130);
if (x_131 == 0)
{
if (x_129 == 0)
{
uint8_t x_132; 
lean_dec(x_100);
lean_dec(x_40);
x_132 = l_Lean_Expr_isFVar(x_98);
if (x_132 == 0)
{
lean_dec(x_99);
lean_dec(x_98);
lean_free_object(x_31);
lean_dec(x_33);
lean_inc(x_3);
x_14 = x_3;
x_15 = x_97;
goto block_28;
}
else
{
lean_object* x_133; uint8_t x_134; lean_object* x_135; uint8_t x_136; 
x_133 = l_Lean_Expr_fvarId_x21(x_98);
lean_dec(x_98);
x_134 = lean_name_eq(x_133, x_1);
lean_dec(x_133);
lean_inc(x_2);
x_135 = l_Lean_MetavarContext_exprDependsOn(x_2, x_99, x_1);
x_136 = lean_unbox(x_135);
lean_dec(x_135);
if (x_136 == 0)
{
if (x_134 == 0)
{
lean_free_object(x_31);
lean_dec(x_33);
lean_inc(x_3);
x_14 = x_3;
x_15 = x_97;
goto block_28;
}
else
{
lean_object* x_137; uint8_t x_138; lean_object* x_139; lean_object* x_140; 
x_137 = l_Lean_LocalDecl_fvarId(x_33);
lean_dec(x_33);
x_138 = 0;
x_139 = lean_box(x_138);
x_140 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_140, 0, x_137);
lean_ctor_set(x_140, 1, x_139);
lean_ctor_set(x_31, 0, x_140);
x_14 = x_31;
x_15 = x_97;
goto block_28;
}
}
else
{
lean_free_object(x_31);
lean_dec(x_33);
lean_inc(x_3);
x_14 = x_3;
x_15 = x_97;
goto block_28;
}
}
}
else
{
uint8_t x_141; 
lean_free_object(x_31);
x_141 = 1;
x_101 = x_141;
goto block_117;
}
}
else
{
if (x_129 == 0)
{
uint8_t x_142; 
lean_dec(x_100);
lean_dec(x_40);
x_142 = l_Lean_Expr_isFVar(x_98);
if (x_142 == 0)
{
lean_dec(x_99);
lean_dec(x_98);
lean_free_object(x_31);
lean_dec(x_33);
lean_inc(x_3);
x_14 = x_3;
x_15 = x_97;
goto block_28;
}
else
{
lean_object* x_143; uint8_t x_144; lean_object* x_145; uint8_t x_146; 
x_143 = l_Lean_Expr_fvarId_x21(x_98);
lean_dec(x_98);
x_144 = lean_name_eq(x_143, x_1);
lean_dec(x_143);
lean_inc(x_2);
x_145 = l_Lean_MetavarContext_exprDependsOn(x_2, x_99, x_1);
x_146 = lean_unbox(x_145);
lean_dec(x_145);
if (x_146 == 0)
{
if (x_144 == 0)
{
lean_free_object(x_31);
lean_dec(x_33);
lean_inc(x_3);
x_14 = x_3;
x_15 = x_97;
goto block_28;
}
else
{
lean_object* x_147; uint8_t x_148; lean_object* x_149; lean_object* x_150; 
x_147 = l_Lean_LocalDecl_fvarId(x_33);
lean_dec(x_33);
x_148 = 0;
x_149 = lean_box(x_148);
x_150 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_150, 0, x_147);
lean_ctor_set(x_150, 1, x_149);
lean_ctor_set(x_31, 0, x_150);
x_14 = x_31;
x_15 = x_97;
goto block_28;
}
}
else
{
lean_free_object(x_31);
lean_dec(x_33);
lean_inc(x_3);
x_14 = x_3;
x_15 = x_97;
goto block_28;
}
}
}
else
{
uint8_t x_151; 
lean_free_object(x_31);
x_151 = 0;
x_101 = x_151;
goto block_117;
}
}
}
block_117:
{
if (x_101 == 0)
{
uint8_t x_102; 
x_102 = l_Lean_Expr_isFVar(x_98);
if (x_102 == 0)
{
lean_dec(x_100);
lean_dec(x_99);
lean_dec(x_98);
lean_dec(x_40);
lean_dec(x_33);
lean_inc(x_3);
x_14 = x_3;
x_15 = x_97;
goto block_28;
}
else
{
lean_object* x_103; uint8_t x_104; lean_object* x_105; uint8_t x_106; 
x_103 = l_Lean_Expr_fvarId_x21(x_98);
lean_dec(x_98);
x_104 = lean_name_eq(x_103, x_1);
lean_dec(x_103);
lean_inc(x_2);
x_105 = l_Lean_MetavarContext_exprDependsOn(x_2, x_99, x_1);
x_106 = lean_unbox(x_105);
lean_dec(x_105);
if (x_106 == 0)
{
if (x_104 == 0)
{
lean_dec(x_100);
lean_dec(x_40);
lean_dec(x_33);
lean_inc(x_3);
x_14 = x_3;
x_15 = x_97;
goto block_28;
}
else
{
lean_object* x_107; uint8_t x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_107 = l_Lean_LocalDecl_fvarId(x_33);
lean_dec(x_33);
x_108 = 0;
x_109 = lean_box(x_108);
if (lean_is_scalar(x_100)) {
 x_110 = lean_alloc_ctor(0, 2, 0);
} else {
 x_110 = x_100;
}
lean_ctor_set(x_110, 0, x_107);
lean_ctor_set(x_110, 1, x_109);
if (lean_is_scalar(x_40)) {
 x_111 = lean_alloc_ctor(1, 1, 0);
} else {
 x_111 = x_40;
}
lean_ctor_set(x_111, 0, x_110);
x_14 = x_111;
x_15 = x_97;
goto block_28;
}
}
else
{
lean_dec(x_100);
lean_dec(x_40);
lean_dec(x_33);
lean_inc(x_3);
x_14 = x_3;
x_15 = x_97;
goto block_28;
}
}
}
else
{
lean_object* x_112; uint8_t x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; 
lean_dec(x_99);
lean_dec(x_98);
x_112 = l_Lean_LocalDecl_fvarId(x_33);
lean_dec(x_33);
x_113 = 1;
x_114 = lean_box(x_113);
if (lean_is_scalar(x_100)) {
 x_115 = lean_alloc_ctor(0, 2, 0);
} else {
 x_115 = x_100;
}
lean_ctor_set(x_115, 0, x_112);
lean_ctor_set(x_115, 1, x_114);
if (lean_is_scalar(x_40)) {
 x_116 = lean_alloc_ctor(1, 1, 0);
} else {
 x_116 = x_40;
}
lean_ctor_set(x_116, 0, x_115);
x_14 = x_116;
x_15 = x_97;
goto block_28;
}
}
}
}
}
else
{
uint8_t x_152; 
lean_free_object(x_31);
lean_dec(x_33);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_152 = !lean_is_exclusive(x_36);
if (x_152 == 0)
{
return x_36;
}
else
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; 
x_153 = lean_ctor_get(x_36, 0);
x_154 = lean_ctor_get(x_36, 1);
lean_inc(x_154);
lean_inc(x_153);
lean_dec(x_36);
x_155 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_155, 0, x_153);
lean_ctor_set(x_155, 1, x_154);
return x_155;
}
}
}
else
{
lean_free_object(x_31);
lean_dec(x_33);
lean_inc(x_3);
x_14 = x_3;
x_15 = x_13;
goto block_28;
}
}
else
{
lean_object* x_156; uint8_t x_157; 
x_156 = lean_ctor_get(x_31, 0);
lean_inc(x_156);
lean_dec(x_31);
x_157 = l_Lean_LocalDecl_isAuxDecl(x_156);
if (x_157 == 0)
{
lean_object* x_158; lean_object* x_159; 
x_158 = l_Lean_LocalDecl_type(x_156);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_159 = l_Lean_Meta_matchEq_x3f(x_158, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_159) == 0)
{
lean_object* x_160; 
x_160 = lean_ctor_get(x_159, 0);
lean_inc(x_160);
if (lean_obj_tag(x_160) == 0)
{
lean_object* x_161; 
lean_dec(x_156);
x_161 = lean_ctor_get(x_159, 1);
lean_inc(x_161);
lean_dec(x_159);
lean_inc(x_3);
x_14 = x_3;
x_15 = x_161;
goto block_28;
}
else
{
lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; uint8_t x_170; uint8_t x_187; 
x_162 = lean_ctor_get(x_160, 0);
lean_inc(x_162);
if (lean_is_exclusive(x_160)) {
 lean_ctor_release(x_160, 0);
 x_163 = x_160;
} else {
 lean_dec_ref(x_160);
 x_163 = lean_box(0);
}
x_164 = lean_ctor_get(x_162, 1);
lean_inc(x_164);
if (lean_is_exclusive(x_162)) {
 lean_ctor_release(x_162, 0);
 lean_ctor_release(x_162, 1);
 x_165 = x_162;
} else {
 lean_dec_ref(x_162);
 x_165 = lean_box(0);
}
x_166 = lean_ctor_get(x_159, 1);
lean_inc(x_166);
lean_dec(x_159);
x_167 = lean_ctor_get(x_164, 0);
lean_inc(x_167);
x_168 = lean_ctor_get(x_164, 1);
lean_inc(x_168);
if (lean_is_exclusive(x_164)) {
 lean_ctor_release(x_164, 0);
 lean_ctor_release(x_164, 1);
 x_169 = x_164;
} else {
 lean_dec_ref(x_164);
 x_169 = lean_box(0);
}
x_187 = l_Lean_Expr_isFVar(x_168);
if (x_187 == 0)
{
uint8_t x_188; 
lean_dec(x_169);
lean_dec(x_163);
x_188 = l_Lean_Expr_isFVar(x_167);
if (x_188 == 0)
{
lean_dec(x_168);
lean_dec(x_167);
lean_dec(x_165);
lean_dec(x_156);
lean_inc(x_3);
x_14 = x_3;
x_15 = x_166;
goto block_28;
}
else
{
lean_object* x_189; uint8_t x_190; lean_object* x_191; uint8_t x_192; 
x_189 = l_Lean_Expr_fvarId_x21(x_167);
lean_dec(x_167);
x_190 = lean_name_eq(x_189, x_1);
lean_dec(x_189);
lean_inc(x_2);
x_191 = l_Lean_MetavarContext_exprDependsOn(x_2, x_168, x_1);
x_192 = lean_unbox(x_191);
lean_dec(x_191);
if (x_192 == 0)
{
if (x_190 == 0)
{
lean_dec(x_165);
lean_dec(x_156);
lean_inc(x_3);
x_14 = x_3;
x_15 = x_166;
goto block_28;
}
else
{
lean_object* x_193; uint8_t x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; 
x_193 = l_Lean_LocalDecl_fvarId(x_156);
lean_dec(x_156);
x_194 = 0;
x_195 = lean_box(x_194);
if (lean_is_scalar(x_165)) {
 x_196 = lean_alloc_ctor(0, 2, 0);
} else {
 x_196 = x_165;
}
lean_ctor_set(x_196, 0, x_193);
lean_ctor_set(x_196, 1, x_195);
x_197 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_197, 0, x_196);
x_14 = x_197;
x_15 = x_166;
goto block_28;
}
}
else
{
lean_dec(x_165);
lean_dec(x_156);
lean_inc(x_3);
x_14 = x_3;
x_15 = x_166;
goto block_28;
}
}
}
else
{
lean_object* x_198; uint8_t x_199; lean_object* x_200; uint8_t x_201; 
x_198 = l_Lean_Expr_fvarId_x21(x_168);
x_199 = lean_name_eq(x_198, x_1);
lean_dec(x_198);
lean_inc(x_167);
lean_inc(x_2);
x_200 = l_Lean_MetavarContext_exprDependsOn(x_2, x_167, x_1);
x_201 = lean_unbox(x_200);
lean_dec(x_200);
if (x_201 == 0)
{
if (x_199 == 0)
{
uint8_t x_202; 
lean_dec(x_169);
lean_dec(x_163);
x_202 = l_Lean_Expr_isFVar(x_167);
if (x_202 == 0)
{
lean_dec(x_168);
lean_dec(x_167);
lean_dec(x_165);
lean_dec(x_156);
lean_inc(x_3);
x_14 = x_3;
x_15 = x_166;
goto block_28;
}
else
{
lean_object* x_203; uint8_t x_204; lean_object* x_205; uint8_t x_206; 
x_203 = l_Lean_Expr_fvarId_x21(x_167);
lean_dec(x_167);
x_204 = lean_name_eq(x_203, x_1);
lean_dec(x_203);
lean_inc(x_2);
x_205 = l_Lean_MetavarContext_exprDependsOn(x_2, x_168, x_1);
x_206 = lean_unbox(x_205);
lean_dec(x_205);
if (x_206 == 0)
{
if (x_204 == 0)
{
lean_dec(x_165);
lean_dec(x_156);
lean_inc(x_3);
x_14 = x_3;
x_15 = x_166;
goto block_28;
}
else
{
lean_object* x_207; uint8_t x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; 
x_207 = l_Lean_LocalDecl_fvarId(x_156);
lean_dec(x_156);
x_208 = 0;
x_209 = lean_box(x_208);
if (lean_is_scalar(x_165)) {
 x_210 = lean_alloc_ctor(0, 2, 0);
} else {
 x_210 = x_165;
}
lean_ctor_set(x_210, 0, x_207);
lean_ctor_set(x_210, 1, x_209);
x_211 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_211, 0, x_210);
x_14 = x_211;
x_15 = x_166;
goto block_28;
}
}
else
{
lean_dec(x_165);
lean_dec(x_156);
lean_inc(x_3);
x_14 = x_3;
x_15 = x_166;
goto block_28;
}
}
}
else
{
uint8_t x_212; 
lean_dec(x_165);
x_212 = 1;
x_170 = x_212;
goto block_186;
}
}
else
{
if (x_199 == 0)
{
uint8_t x_213; 
lean_dec(x_169);
lean_dec(x_163);
x_213 = l_Lean_Expr_isFVar(x_167);
if (x_213 == 0)
{
lean_dec(x_168);
lean_dec(x_167);
lean_dec(x_165);
lean_dec(x_156);
lean_inc(x_3);
x_14 = x_3;
x_15 = x_166;
goto block_28;
}
else
{
lean_object* x_214; uint8_t x_215; lean_object* x_216; uint8_t x_217; 
x_214 = l_Lean_Expr_fvarId_x21(x_167);
lean_dec(x_167);
x_215 = lean_name_eq(x_214, x_1);
lean_dec(x_214);
lean_inc(x_2);
x_216 = l_Lean_MetavarContext_exprDependsOn(x_2, x_168, x_1);
x_217 = lean_unbox(x_216);
lean_dec(x_216);
if (x_217 == 0)
{
if (x_215 == 0)
{
lean_dec(x_165);
lean_dec(x_156);
lean_inc(x_3);
x_14 = x_3;
x_15 = x_166;
goto block_28;
}
else
{
lean_object* x_218; uint8_t x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; 
x_218 = l_Lean_LocalDecl_fvarId(x_156);
lean_dec(x_156);
x_219 = 0;
x_220 = lean_box(x_219);
if (lean_is_scalar(x_165)) {
 x_221 = lean_alloc_ctor(0, 2, 0);
} else {
 x_221 = x_165;
}
lean_ctor_set(x_221, 0, x_218);
lean_ctor_set(x_221, 1, x_220);
x_222 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_222, 0, x_221);
x_14 = x_222;
x_15 = x_166;
goto block_28;
}
}
else
{
lean_dec(x_165);
lean_dec(x_156);
lean_inc(x_3);
x_14 = x_3;
x_15 = x_166;
goto block_28;
}
}
}
else
{
uint8_t x_223; 
lean_dec(x_165);
x_223 = 0;
x_170 = x_223;
goto block_186;
}
}
}
block_186:
{
if (x_170 == 0)
{
uint8_t x_171; 
x_171 = l_Lean_Expr_isFVar(x_167);
if (x_171 == 0)
{
lean_dec(x_169);
lean_dec(x_168);
lean_dec(x_167);
lean_dec(x_163);
lean_dec(x_156);
lean_inc(x_3);
x_14 = x_3;
x_15 = x_166;
goto block_28;
}
else
{
lean_object* x_172; uint8_t x_173; lean_object* x_174; uint8_t x_175; 
x_172 = l_Lean_Expr_fvarId_x21(x_167);
lean_dec(x_167);
x_173 = lean_name_eq(x_172, x_1);
lean_dec(x_172);
lean_inc(x_2);
x_174 = l_Lean_MetavarContext_exprDependsOn(x_2, x_168, x_1);
x_175 = lean_unbox(x_174);
lean_dec(x_174);
if (x_175 == 0)
{
if (x_173 == 0)
{
lean_dec(x_169);
lean_dec(x_163);
lean_dec(x_156);
lean_inc(x_3);
x_14 = x_3;
x_15 = x_166;
goto block_28;
}
else
{
lean_object* x_176; uint8_t x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; 
x_176 = l_Lean_LocalDecl_fvarId(x_156);
lean_dec(x_156);
x_177 = 0;
x_178 = lean_box(x_177);
if (lean_is_scalar(x_169)) {
 x_179 = lean_alloc_ctor(0, 2, 0);
} else {
 x_179 = x_169;
}
lean_ctor_set(x_179, 0, x_176);
lean_ctor_set(x_179, 1, x_178);
if (lean_is_scalar(x_163)) {
 x_180 = lean_alloc_ctor(1, 1, 0);
} else {
 x_180 = x_163;
}
lean_ctor_set(x_180, 0, x_179);
x_14 = x_180;
x_15 = x_166;
goto block_28;
}
}
else
{
lean_dec(x_169);
lean_dec(x_163);
lean_dec(x_156);
lean_inc(x_3);
x_14 = x_3;
x_15 = x_166;
goto block_28;
}
}
}
else
{
lean_object* x_181; uint8_t x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; 
lean_dec(x_168);
lean_dec(x_167);
x_181 = l_Lean_LocalDecl_fvarId(x_156);
lean_dec(x_156);
x_182 = 1;
x_183 = lean_box(x_182);
if (lean_is_scalar(x_169)) {
 x_184 = lean_alloc_ctor(0, 2, 0);
} else {
 x_184 = x_169;
}
lean_ctor_set(x_184, 0, x_181);
lean_ctor_set(x_184, 1, x_183);
if (lean_is_scalar(x_163)) {
 x_185 = lean_alloc_ctor(1, 1, 0);
} else {
 x_185 = x_163;
}
lean_ctor_set(x_185, 0, x_184);
x_14 = x_185;
x_15 = x_166;
goto block_28;
}
}
}
}
else
{
lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; 
lean_dec(x_156);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_224 = lean_ctor_get(x_159, 0);
lean_inc(x_224);
x_225 = lean_ctor_get(x_159, 1);
lean_inc(x_225);
if (lean_is_exclusive(x_159)) {
 lean_ctor_release(x_159, 0);
 lean_ctor_release(x_159, 1);
 x_226 = x_159;
} else {
 lean_dec_ref(x_159);
 x_226 = lean_box(0);
}
if (lean_is_scalar(x_226)) {
 x_227 = lean_alloc_ctor(1, 2, 0);
} else {
 x_227 = x_226;
}
lean_ctor_set(x_227, 0, x_224);
lean_ctor_set(x_227, 1, x_225);
return x_227;
}
}
else
{
lean_dec(x_156);
lean_inc(x_3);
x_14 = x_3;
x_15 = x_13;
goto block_28;
}
}
}
}
block_28:
{
if (lean_obj_tag(x_14) == 0)
{
size_t x_16; size_t x_17; 
x_16 = 1;
x_17 = x_7 + x_16;
lean_inc(x_4);
{
size_t _tmp_6 = x_17;
lean_object* _tmp_7 = x_4;
lean_object* _tmp_12 = x_15;
x_7 = _tmp_6;
x_8 = _tmp_7;
x_13 = _tmp_12;
}
goto _start;
}
else
{
uint8_t x_19; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_19 = !lean_is_exclusive(x_14);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_box(0);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_14);
lean_ctor_set(x_21, 1, x_20);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_15);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_23 = lean_ctor_get(x_14, 0);
lean_inc(x_23);
lean_dec(x_14);
x_24 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_24, 0, x_23);
x_25 = lean_box(0);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_15);
return x_27;
}
}
}
}
}
lean_object* l_Std_PersistentArray_findSomeM_x3f___at_Lean_Meta_subst___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_3, 0);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_2);
x_10 = l_Std_PersistentArray_findSomeMAux___at_Lean_Meta_subst___spec__3(x_1, x_2, x_9, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; size_t x_16; size_t x_17; lean_object* x_18; lean_object* x_19; 
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_ctor_get(x_3, 1);
x_14 = lean_box(0);
x_15 = lean_array_get_size(x_13);
x_16 = lean_usize_of_nat(x_15);
lean_dec(x_15);
x_17 = 0;
x_18 = l_Array_findSomeM_x3f___rarg___closed__1;
x_19 = l_Array_forInUnsafe_loop___at_Lean_Meta_subst___spec__6(x_1, x_2, x_14, x_18, x_13, x_16, x_17, x_18, x_4, x_5, x_6, x_7, x_12);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
lean_dec(x_20);
if (lean_obj_tag(x_21) == 0)
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_19);
if (x_22 == 0)
{
lean_object* x_23; 
x_23 = lean_ctor_get(x_19, 0);
lean_dec(x_23);
lean_ctor_set(x_19, 0, x_14);
return x_19;
}
else
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_19, 1);
lean_inc(x_24);
lean_dec(x_19);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_14);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
else
{
uint8_t x_26; 
x_26 = !lean_is_exclusive(x_19);
if (x_26 == 0)
{
lean_object* x_27; uint8_t x_28; 
x_27 = lean_ctor_get(x_19, 0);
lean_dec(x_27);
x_28 = !lean_is_exclusive(x_21);
if (x_28 == 0)
{
lean_ctor_set(x_19, 0, x_21);
return x_19;
}
else
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_21, 0);
lean_inc(x_29);
lean_dec(x_21);
x_30 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_19, 0, x_30);
return x_19;
}
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_31 = lean_ctor_get(x_19, 1);
lean_inc(x_31);
lean_dec(x_19);
x_32 = lean_ctor_get(x_21, 0);
lean_inc(x_32);
if (lean_is_exclusive(x_21)) {
 lean_ctor_release(x_21, 0);
 x_33 = x_21;
} else {
 lean_dec_ref(x_21);
 x_33 = lean_box(0);
}
if (lean_is_scalar(x_33)) {
 x_34 = lean_alloc_ctor(1, 1, 0);
} else {
 x_34 = x_33;
}
lean_ctor_set(x_34, 0, x_32);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_31);
return x_35;
}
}
}
else
{
uint8_t x_36; 
x_36 = !lean_is_exclusive(x_19);
if (x_36 == 0)
{
return x_19;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_19, 0);
x_38 = lean_ctor_get(x_19, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_19);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
}
else
{
uint8_t x_40; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_40 = !lean_is_exclusive(x_10);
if (x_40 == 0)
{
lean_object* x_41; uint8_t x_42; 
x_41 = lean_ctor_get(x_10, 0);
lean_dec(x_41);
x_42 = !lean_is_exclusive(x_11);
if (x_42 == 0)
{
return x_10;
}
else
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_ctor_get(x_11, 0);
lean_inc(x_43);
lean_dec(x_11);
x_44 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_10, 0, x_44);
return x_10;
}
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_45 = lean_ctor_get(x_10, 1);
lean_inc(x_45);
lean_dec(x_10);
x_46 = lean_ctor_get(x_11, 0);
lean_inc(x_46);
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 x_47 = x_11;
} else {
 lean_dec_ref(x_11);
 x_47 = lean_box(0);
}
if (lean_is_scalar(x_47)) {
 x_48 = lean_alloc_ctor(1, 1, 0);
} else {
 x_48 = x_47;
}
lean_ctor_set(x_48, 0, x_46);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_45);
return x_49;
}
}
}
else
{
uint8_t x_50; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_50 = !lean_is_exclusive(x_10);
if (x_50 == 0)
{
return x_10;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_10, 0);
x_52 = lean_ctor_get(x_10, 1);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_10);
x_53 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
return x_53;
}
}
}
}
lean_object* l_Lean_LocalContext_findDeclM_x3f___at_Lean_Meta_subst___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_3, 1);
x_10 = l_Std_PersistentArray_findSomeM_x3f___at_Lean_Meta_subst___spec__2(x_1, x_2, x_9, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
static lean_object* _init_l_Lean_Meta_subst___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("did not find equation for eliminating '");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_subst___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_subst___lambda__1___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_subst___lambda__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid equality proof, it is not of the form (x = t) or (t = x)");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_subst___lambda__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_subst___lambda__1___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
lean_object* l_Lean_Meta_subst___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; 
x_9 = l_Lean_LocalDecl_type(x_3);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_9);
x_10 = l_Lean_Meta_matchEq_x3f(x_9, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_dec(x_9);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_st_ref_get(x_5, x_12);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_ctor_get(x_14, 0);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_ctor_get(x_4, 1);
lean_inc(x_17);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_18 = l_Lean_LocalContext_findDeclM_x3f___at_Lean_Meta_subst___spec__1(x_1, x_16, x_17, x_4, x_5, x_6, x_7, x_15);
lean_dec(x_17);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = l_Lean_mkFVar(x_1);
x_22 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_22, 0, x_21);
x_23 = l_Lean_Meta_subst___lambda__1___closed__2;
x_24 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_22);
x_25 = l_Lean_throwUnknownConstant___rarg___closed__3;
x_26 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
x_27 = l_Lean_Meta_substCore___lambda__13___closed__2;
x_28 = lean_box(0);
x_29 = l_Lean_Meta_throwTacticEx___rarg(x_27, x_2, x_26, x_28, x_4, x_5, x_6, x_7, x_20);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_29;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; uint8_t x_36; lean_object* x_37; 
lean_dec(x_1);
x_30 = lean_ctor_get(x_19, 0);
lean_inc(x_30);
lean_dec(x_19);
x_31 = lean_ctor_get(x_18, 1);
lean_inc(x_31);
lean_dec(x_18);
x_32 = lean_ctor_get(x_30, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_30, 1);
lean_inc(x_33);
lean_dec(x_30);
x_34 = lean_box(0);
x_35 = 1;
x_36 = lean_unbox(x_33);
lean_dec(x_33);
x_37 = l_Lean_Meta_substCore(x_2, x_32, x_36, x_34, x_35, x_4, x_5, x_6, x_7, x_31);
if (lean_obj_tag(x_37) == 0)
{
uint8_t x_38; 
x_38 = !lean_is_exclusive(x_37);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; 
x_39 = lean_ctor_get(x_37, 0);
x_40 = lean_ctor_get(x_39, 1);
lean_inc(x_40);
lean_dec(x_39);
lean_ctor_set(x_37, 0, x_40);
return x_37;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_41 = lean_ctor_get(x_37, 0);
x_42 = lean_ctor_get(x_37, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_37);
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
lean_dec(x_41);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_42);
return x_44;
}
}
else
{
uint8_t x_45; 
x_45 = !lean_is_exclusive(x_37);
if (x_45 == 0)
{
return x_37;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_37, 0);
x_47 = lean_ctor_get(x_37, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_37);
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
return x_48;
}
}
}
}
else
{
uint8_t x_49; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_49 = !lean_is_exclusive(x_18);
if (x_49 == 0)
{
return x_18;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_18, 0);
x_51 = lean_ctor_get(x_18, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_18);
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
return x_52;
}
}
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_53 = lean_ctor_get(x_11, 0);
lean_inc(x_53);
lean_dec(x_11);
x_54 = lean_ctor_get(x_53, 1);
lean_inc(x_54);
lean_dec(x_53);
x_55 = lean_ctor_get(x_10, 1);
lean_inc(x_55);
lean_dec(x_10);
x_56 = lean_ctor_get(x_54, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_54, 1);
lean_inc(x_57);
lean_dec(x_54);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_58 = l_Lean_Meta_whnf___at___private_Lean_Meta_Basic_0__Lean_Meta_isClassExpensive_x3f___spec__2(x_57, x_4, x_5, x_6, x_7, x_55);
if (lean_obj_tag(x_58) == 0)
{
lean_object* x_59; lean_object* x_60; uint8_t x_61; 
x_59 = lean_ctor_get(x_58, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_58, 1);
lean_inc(x_60);
lean_dec(x_58);
x_61 = l_Lean_Expr_isFVar(x_59);
lean_dec(x_59);
if (x_61 == 0)
{
lean_object* x_62; 
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_62 = l_Lean_Meta_whnf___at___private_Lean_Meta_Basic_0__Lean_Meta_isClassExpensive_x3f___spec__2(x_56, x_4, x_5, x_6, x_7, x_60);
if (lean_obj_tag(x_62) == 0)
{
lean_object* x_63; lean_object* x_64; uint8_t x_65; 
x_63 = lean_ctor_get(x_62, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_62, 1);
lean_inc(x_64);
lean_dec(x_62);
x_65 = l_Lean_Expr_isFVar(x_63);
lean_dec(x_63);
if (x_65 == 0)
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
lean_dec(x_1);
x_66 = l_Lean_indentExpr(x_9);
x_67 = l_Lean_Meta_subst___lambda__1___closed__4;
x_68 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_68, 0, x_67);
lean_ctor_set(x_68, 1, x_66);
x_69 = l_Array_foldlMUnsafe_fold___at_Lean_withNestedTraces___spec__5___closed__1;
x_70 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_70, 0, x_68);
lean_ctor_set(x_70, 1, x_69);
x_71 = l_Lean_Meta_substCore___lambda__13___closed__2;
x_72 = lean_box(0);
x_73 = l_Lean_Meta_throwTacticEx___rarg(x_71, x_2, x_70, x_72, x_4, x_5, x_6, x_7, x_64);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_73;
}
else
{
lean_object* x_74; uint8_t x_75; uint8_t x_76; lean_object* x_77; 
lean_dec(x_9);
x_74 = lean_box(0);
x_75 = 0;
x_76 = 1;
x_77 = l_Lean_Meta_substCore(x_2, x_1, x_75, x_74, x_76, x_4, x_5, x_6, x_7, x_64);
if (lean_obj_tag(x_77) == 0)
{
uint8_t x_78; 
x_78 = !lean_is_exclusive(x_77);
if (x_78 == 0)
{
lean_object* x_79; lean_object* x_80; 
x_79 = lean_ctor_get(x_77, 0);
x_80 = lean_ctor_get(x_79, 1);
lean_inc(x_80);
lean_dec(x_79);
lean_ctor_set(x_77, 0, x_80);
return x_77;
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_81 = lean_ctor_get(x_77, 0);
x_82 = lean_ctor_get(x_77, 1);
lean_inc(x_82);
lean_inc(x_81);
lean_dec(x_77);
x_83 = lean_ctor_get(x_81, 1);
lean_inc(x_83);
lean_dec(x_81);
x_84 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_84, 0, x_83);
lean_ctor_set(x_84, 1, x_82);
return x_84;
}
}
else
{
uint8_t x_85; 
x_85 = !lean_is_exclusive(x_77);
if (x_85 == 0)
{
return x_77;
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_86 = lean_ctor_get(x_77, 0);
x_87 = lean_ctor_get(x_77, 1);
lean_inc(x_87);
lean_inc(x_86);
lean_dec(x_77);
x_88 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_88, 0, x_86);
lean_ctor_set(x_88, 1, x_87);
return x_88;
}
}
}
}
else
{
uint8_t x_89; 
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_89 = !lean_is_exclusive(x_62);
if (x_89 == 0)
{
return x_62;
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_90 = lean_ctor_get(x_62, 0);
x_91 = lean_ctor_get(x_62, 1);
lean_inc(x_91);
lean_inc(x_90);
lean_dec(x_62);
x_92 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_92, 0, x_90);
lean_ctor_set(x_92, 1, x_91);
return x_92;
}
}
}
else
{
lean_object* x_93; uint8_t x_94; lean_object* x_95; 
lean_dec(x_56);
lean_dec(x_9);
x_93 = lean_box(0);
x_94 = 1;
x_95 = l_Lean_Meta_substCore(x_2, x_1, x_94, x_93, x_94, x_4, x_5, x_6, x_7, x_60);
if (lean_obj_tag(x_95) == 0)
{
uint8_t x_96; 
x_96 = !lean_is_exclusive(x_95);
if (x_96 == 0)
{
lean_object* x_97; lean_object* x_98; 
x_97 = lean_ctor_get(x_95, 0);
x_98 = lean_ctor_get(x_97, 1);
lean_inc(x_98);
lean_dec(x_97);
lean_ctor_set(x_95, 0, x_98);
return x_95;
}
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_99 = lean_ctor_get(x_95, 0);
x_100 = lean_ctor_get(x_95, 1);
lean_inc(x_100);
lean_inc(x_99);
lean_dec(x_95);
x_101 = lean_ctor_get(x_99, 1);
lean_inc(x_101);
lean_dec(x_99);
x_102 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_102, 0, x_101);
lean_ctor_set(x_102, 1, x_100);
return x_102;
}
}
else
{
uint8_t x_103; 
x_103 = !lean_is_exclusive(x_95);
if (x_103 == 0)
{
return x_95;
}
else
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; 
x_104 = lean_ctor_get(x_95, 0);
x_105 = lean_ctor_get(x_95, 1);
lean_inc(x_105);
lean_inc(x_104);
lean_dec(x_95);
x_106 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_106, 0, x_104);
lean_ctor_set(x_106, 1, x_105);
return x_106;
}
}
}
}
else
{
uint8_t x_107; 
lean_dec(x_56);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_107 = !lean_is_exclusive(x_58);
if (x_107 == 0)
{
return x_58;
}
else
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; 
x_108 = lean_ctor_get(x_58, 0);
x_109 = lean_ctor_get(x_58, 1);
lean_inc(x_109);
lean_inc(x_108);
lean_dec(x_58);
x_110 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_110, 0, x_108);
lean_ctor_set(x_110, 1, x_109);
return x_110;
}
}
}
}
else
{
uint8_t x_111; 
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_111 = !lean_is_exclusive(x_10);
if (x_111 == 0)
{
return x_10;
}
else
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; 
x_112 = lean_ctor_get(x_10, 0);
x_113 = lean_ctor_get(x_10, 1);
lean_inc(x_113);
lean_inc(x_112);
lean_dec(x_10);
x_114 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_114, 0, x_112);
lean_ctor_set(x_114, 1, x_113);
return x_114;
}
}
}
}
lean_object* l_Lean_Meta_subst(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
lean_inc(x_2);
x_8 = lean_alloc_closure((void*)(l_Lean_Meta_getLocalDecl___at_Lean_Meta_getFVarLocalDecl___spec__1___boxed), 6, 1);
lean_closure_set(x_8, 0, x_2);
lean_inc(x_1);
x_9 = lean_alloc_closure((void*)(l_Lean_Meta_subst___lambda__1___boxed), 8, 2);
lean_closure_set(x_9, 0, x_2);
lean_closure_set(x_9, 1, x_1);
x_10 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_Lean_Meta_Basic___instance__8___spec__2___rarg), 7, 2);
lean_closure_set(x_10, 0, x_8);
lean_closure_set(x_10, 1, x_9);
x_11 = l_Lean_Meta_withMVarContext___at_Lean_Meta_admit___spec__2___rarg(x_1, x_10, x_3, x_4, x_5, x_6, x_7);
return x_11;
}
}
lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_subst___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
size_t x_13; size_t x_14; lean_object* x_15; 
x_13 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_14 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_15 = l_Array_forInUnsafe_loop___at_Lean_Meta_subst___spec__4(x_1, x_2, x_3, x_4, x_13, x_14, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_4);
lean_dec(x_1);
return x_15;
}
}
lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_subst___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
size_t x_14; size_t x_15; lean_object* x_16; 
x_14 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_15 = lean_unbox_usize(x_7);
lean_dec(x_7);
x_16 = l_Array_forInUnsafe_loop___at_Lean_Meta_subst___spec__5(x_1, x_2, x_3, x_4, x_5, x_14, x_15, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_5);
lean_dec(x_1);
return x_16;
}
}
lean_object* l_Std_PersistentArray_findSomeMAux___at_Lean_Meta_subst___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Std_PersistentArray_findSomeMAux___at_Lean_Meta_subst___spec__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_3);
lean_dec(x_1);
return x_9;
}
}
lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_subst___spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
size_t x_14; size_t x_15; lean_object* x_16; 
x_14 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_15 = lean_unbox_usize(x_7);
lean_dec(x_7);
x_16 = l_Array_forInUnsafe_loop___at_Lean_Meta_subst___spec__6(x_1, x_2, x_3, x_4, x_5, x_14, x_15, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_5);
lean_dec(x_1);
return x_16;
}
}
lean_object* l_Std_PersistentArray_findSomeM_x3f___at_Lean_Meta_subst___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Std_PersistentArray_findSomeM_x3f___at_Lean_Meta_subst___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_3);
lean_dec(x_1);
return x_9;
}
}
lean_object* l_Lean_LocalContext_findDeclM_x3f___at_Lean_Meta_subst___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_LocalContext_findDeclM_x3f___at_Lean_Meta_subst___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_3);
lean_dec(x_1);
return x_9;
}
}
lean_object* l_Lean_Meta_subst___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_subst___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_3);
return x_9;
}
}
lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Subst___hyg_1143_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Meta_substCore___lambda__13___closed__18;
x_3 = l_Lean_registerTraceClass(x_2, x_1);
return x_3;
}
}
lean_object* initialize_Init(lean_object*);
lean_object* initialize_Lean_Meta_AppBuilder(lean_object*);
lean_object* initialize_Lean_Meta_MatchUtil(lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Util(lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Revert(lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Intro(lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Clear(lean_object*);
lean_object* initialize_Lean_Meta_Tactic_FVarSubst(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Lean_Meta_Tactic_Subst(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_AppBuilder(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_MatchUtil(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Util(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Revert(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Intro(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Clear(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_FVarSubst(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Meta_substCore___lambda__11___closed__1 = _init_l_Lean_Meta_substCore___lambda__11___closed__1();
lean_mark_persistent(l_Lean_Meta_substCore___lambda__11___closed__1);
l_Lean_Meta_substCore___lambda__11___closed__2 = _init_l_Lean_Meta_substCore___lambda__11___closed__2();
lean_mark_persistent(l_Lean_Meta_substCore___lambda__11___closed__2);
l_Lean_Meta_substCore___lambda__11___closed__3 = _init_l_Lean_Meta_substCore___lambda__11___closed__3();
lean_mark_persistent(l_Lean_Meta_substCore___lambda__11___closed__3);
l_Lean_Meta_substCore___lambda__11___closed__4 = _init_l_Lean_Meta_substCore___lambda__11___closed__4();
lean_mark_persistent(l_Lean_Meta_substCore___lambda__11___closed__4);
l_Lean_Meta_substCore___lambda__11___closed__5 = _init_l_Lean_Meta_substCore___lambda__11___closed__5();
lean_mark_persistent(l_Lean_Meta_substCore___lambda__11___closed__5);
l_Lean_Meta_substCore___lambda__12___closed__1 = _init_l_Lean_Meta_substCore___lambda__12___closed__1();
lean_mark_persistent(l_Lean_Meta_substCore___lambda__12___closed__1);
l_Lean_Meta_substCore___lambda__12___closed__2 = _init_l_Lean_Meta_substCore___lambda__12___closed__2();
lean_mark_persistent(l_Lean_Meta_substCore___lambda__12___closed__2);
l_Lean_Meta_substCore___lambda__13___closed__1 = _init_l_Lean_Meta_substCore___lambda__13___closed__1();
lean_mark_persistent(l_Lean_Meta_substCore___lambda__13___closed__1);
l_Lean_Meta_substCore___lambda__13___closed__2 = _init_l_Lean_Meta_substCore___lambda__13___closed__2();
lean_mark_persistent(l_Lean_Meta_substCore___lambda__13___closed__2);
l_Lean_Meta_substCore___lambda__13___closed__3 = _init_l_Lean_Meta_substCore___lambda__13___closed__3();
lean_mark_persistent(l_Lean_Meta_substCore___lambda__13___closed__3);
l_Lean_Meta_substCore___lambda__13___closed__4 = _init_l_Lean_Meta_substCore___lambda__13___closed__4();
lean_mark_persistent(l_Lean_Meta_substCore___lambda__13___closed__4);
l_Lean_Meta_substCore___lambda__13___closed__5 = _init_l_Lean_Meta_substCore___lambda__13___closed__5();
lean_mark_persistent(l_Lean_Meta_substCore___lambda__13___closed__5);
l_Lean_Meta_substCore___lambda__13___closed__6 = _init_l_Lean_Meta_substCore___lambda__13___closed__6();
lean_mark_persistent(l_Lean_Meta_substCore___lambda__13___closed__6);
l_Lean_Meta_substCore___lambda__13___closed__7 = _init_l_Lean_Meta_substCore___lambda__13___closed__7();
lean_mark_persistent(l_Lean_Meta_substCore___lambda__13___closed__7);
l_Lean_Meta_substCore___lambda__13___closed__8 = _init_l_Lean_Meta_substCore___lambda__13___closed__8();
lean_mark_persistent(l_Lean_Meta_substCore___lambda__13___closed__8);
l_Lean_Meta_substCore___lambda__13___closed__9 = _init_l_Lean_Meta_substCore___lambda__13___closed__9();
lean_mark_persistent(l_Lean_Meta_substCore___lambda__13___closed__9);
l_Lean_Meta_substCore___lambda__13___closed__10 = _init_l_Lean_Meta_substCore___lambda__13___closed__10();
lean_mark_persistent(l_Lean_Meta_substCore___lambda__13___closed__10);
l_Lean_Meta_substCore___lambda__13___closed__11 = _init_l_Lean_Meta_substCore___lambda__13___closed__11();
lean_mark_persistent(l_Lean_Meta_substCore___lambda__13___closed__11);
l_Lean_Meta_substCore___lambda__13___closed__12 = _init_l_Lean_Meta_substCore___lambda__13___closed__12();
lean_mark_persistent(l_Lean_Meta_substCore___lambda__13___closed__12);
l_Lean_Meta_substCore___lambda__13___closed__13 = _init_l_Lean_Meta_substCore___lambda__13___closed__13();
lean_mark_persistent(l_Lean_Meta_substCore___lambda__13___closed__13);
l_Lean_Meta_substCore___lambda__13___closed__14 = _init_l_Lean_Meta_substCore___lambda__13___closed__14();
lean_mark_persistent(l_Lean_Meta_substCore___lambda__13___closed__14);
l_Lean_Meta_substCore___lambda__13___closed__15 = _init_l_Lean_Meta_substCore___lambda__13___closed__15();
lean_mark_persistent(l_Lean_Meta_substCore___lambda__13___closed__15);
l_Lean_Meta_substCore___lambda__13___closed__16 = _init_l_Lean_Meta_substCore___lambda__13___closed__16();
lean_mark_persistent(l_Lean_Meta_substCore___lambda__13___closed__16);
l_Lean_Meta_substCore___lambda__13___closed__17 = _init_l_Lean_Meta_substCore___lambda__13___closed__17();
lean_mark_persistent(l_Lean_Meta_substCore___lambda__13___closed__17);
l_Lean_Meta_substCore___lambda__13___closed__18 = _init_l_Lean_Meta_substCore___lambda__13___closed__18();
lean_mark_persistent(l_Lean_Meta_substCore___lambda__13___closed__18);
l_Lean_Meta_substCore___lambda__13___closed__19 = _init_l_Lean_Meta_substCore___lambda__13___closed__19();
lean_mark_persistent(l_Lean_Meta_substCore___lambda__13___closed__19);
l_Lean_Meta_substCore___lambda__13___closed__20 = _init_l_Lean_Meta_substCore___lambda__13___closed__20();
lean_mark_persistent(l_Lean_Meta_substCore___lambda__13___closed__20);
l_Lean_Meta_substCore___lambda__13___closed__21 = _init_l_Lean_Meta_substCore___lambda__13___closed__21();
lean_mark_persistent(l_Lean_Meta_substCore___lambda__13___closed__21);
l_Lean_Meta_substCore___lambda__13___closed__22 = _init_l_Lean_Meta_substCore___lambda__13___closed__22();
lean_mark_persistent(l_Lean_Meta_substCore___lambda__13___closed__22);
l_Lean_Meta_substCore___lambda__13___closed__23 = _init_l_Lean_Meta_substCore___lambda__13___closed__23();
lean_mark_persistent(l_Lean_Meta_substCore___lambda__13___closed__23);
l_Lean_Meta_substCore___lambda__13___closed__24 = _init_l_Lean_Meta_substCore___lambda__13___closed__24();
lean_mark_persistent(l_Lean_Meta_substCore___lambda__13___closed__24);
l_Lean_Meta_substCore___lambda__13___closed__25 = _init_l_Lean_Meta_substCore___lambda__13___closed__25();
lean_mark_persistent(l_Lean_Meta_substCore___lambda__13___closed__25);
l_Lean_Meta_substCore___lambda__13___closed__26 = _init_l_Lean_Meta_substCore___lambda__13___closed__26();
lean_mark_persistent(l_Lean_Meta_substCore___lambda__13___closed__26);
l_Lean_Meta_subst___lambda__1___closed__1 = _init_l_Lean_Meta_subst___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Meta_subst___lambda__1___closed__1);
l_Lean_Meta_subst___lambda__1___closed__2 = _init_l_Lean_Meta_subst___lambda__1___closed__2();
lean_mark_persistent(l_Lean_Meta_subst___lambda__1___closed__2);
l_Lean_Meta_subst___lambda__1___closed__3 = _init_l_Lean_Meta_subst___lambda__1___closed__3();
lean_mark_persistent(l_Lean_Meta_subst___lambda__1___closed__3);
l_Lean_Meta_subst___lambda__1___closed__4 = _init_l_Lean_Meta_subst___lambda__1___closed__4();
lean_mark_persistent(l_Lean_Meta_subst___lambda__1___closed__4);
res = l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Subst___hyg_1143_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
