// Lean compiler output
// Module: LoVe.LoVe01_TypesAndTerms_Demo
// Imports: Init LoVe.LoVelib
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
LEAN_EXPORT lean_object* l_LoVe_g___boxed(lean_object*, lean_object*);
static lean_object* l_LoVe_a___closed__1;
LEAN_EXPORT lean_object* l_LoVe_f(lean_object*);
lean_object* lean_nat_to_int(lean_object*);
LEAN_EXPORT lean_object* l_LoVe_g(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_LoVe_someFunOfType(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_LoVe_f___boxed(lean_object*);
LEAN_EXPORT lean_object* l_LoVe_b;
LEAN_EXPORT lean_object* l_LoVe_someFunOfType___lambda__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_LoVe_someFunOfType___lambda__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_LoVe_a;
static lean_object* _init_l_LoVe_a___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_LoVe_a() {
_start:
{
lean_object* x_1; 
x_1 = l_LoVe_a___closed__1;
return x_1;
}
}
static lean_object* _init_l_LoVe_b() {
_start:
{
lean_object* x_1; 
x_1 = l_LoVe_a___closed__1;
return x_1;
}
}
LEAN_EXPORT lean_object* l_LoVe_f(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_LoVe_a___closed__1;
return x_2;
}
}
LEAN_EXPORT lean_object* l_LoVe_f___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_LoVe_f(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_LoVe_g(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_LoVe_a___closed__1;
return x_3;
}
}
LEAN_EXPORT lean_object* l_LoVe_g___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_LoVe_g(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_LoVe_someFunOfType___lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_LoVe_someFunOfType(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
lean_inc(x_3);
x_4 = lean_alloc_closure((void*)(l_LoVe_someFunOfType___lambda__1___boxed), 2, 1);
lean_closure_set(x_4, 0, x_3);
x_5 = lean_apply_1(x_2, x_4);
x_6 = lean_apply_2(x_1, x_3, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_LoVe_someFunOfType___lambda__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_LoVe_someFunOfType___lambda__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_LoVe_LoVelib(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_LoVe_LoVe01__TypesAndTerms__Demo(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_LoVe_LoVelib(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_LoVe_a___closed__1 = _init_l_LoVe_a___closed__1();
lean_mark_persistent(l_LoVe_a___closed__1);
l_LoVe_a = _init_l_LoVe_a();
lean_mark_persistent(l_LoVe_a);
l_LoVe_b = _init_l_LoVe_b();
lean_mark_persistent(l_LoVe_b);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
