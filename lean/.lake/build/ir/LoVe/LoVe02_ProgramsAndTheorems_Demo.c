// Lean compiler output
// Module: LoVe.LoVe02_ProgramsAndTheorems_Demo
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
LEAN_EXPORT lean_object* l_LoVe_reverse(lean_object*);
LEAN_EXPORT lean_object* l_LoVe_appendImplicit___rarg(lean_object*, lean_object*);
static lean_object* l_LoVe_SorryTheorems_a___closed__1;
LEAN_EXPORT lean_object* l_LoVe_mul(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_LoVe_powerIter(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_LoVe_fib___boxed(lean_object*);
LEAN_EXPORT lean_object* l_LoVe_appendImplicit(lean_object*);
LEAN_EXPORT lean_object* l_LoVe_power(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_LoVe_iter___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_LoVe_reverse___rarg(lean_object*);
lean_object* l_List_appendTR___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_LoVe_SorryTheorems_a;
LEAN_EXPORT lean_object* l_LoVe_append(lean_object*);
lean_object* lean_nat_to_int(lean_object*);
LEAN_EXPORT lean_object* l_LoVe_powerParam(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_LoVe_add___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_LoVe_SorryTheorems_b;
LEAN_EXPORT lean_object* l_LoVe_append___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_LoVe_power___boxed(lean_object*, lean_object*);
lean_object* lean_int_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_LoVe_fib(lean_object*);
lean_object* lean_int_mul(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_LoVe_appendImplicit___rarg___boxed(lean_object*, lean_object*);
lean_object* lean_int_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_LoVe_iter(lean_object*);
LEAN_EXPORT lean_object* l_LoVe_append___rarg___boxed(lean_object*, lean_object*);
lean_object* l_Int_ediv(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_LoVe_eval(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_LoVe_powerIter___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_LoVe_appendPretty(lean_object*);
LEAN_EXPORT lean_object* l_LoVe_mul___boxed(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_LoVe_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_LoVe_appendPretty___rarg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_LoVe_powerParam___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_LoVe_iter___rarg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_LoVe_appendPretty___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_LoVe_fib(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_nat_dec_eq(x_1, x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_unsigned_to_nat(1u);
x_5 = lean_nat_sub(x_1, x_4);
x_6 = lean_nat_dec_eq(x_5, x_2);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_7 = lean_nat_sub(x_5, x_4);
lean_dec(x_5);
x_8 = lean_nat_add(x_7, x_4);
x_9 = l_LoVe_fib(x_8);
lean_dec(x_8);
x_10 = l_LoVe_fib(x_7);
lean_dec(x_7);
x_11 = lean_nat_add(x_9, x_10);
lean_dec(x_10);
lean_dec(x_9);
return x_11;
}
else
{
lean_object* x_12; 
lean_dec(x_5);
x_12 = lean_unsigned_to_nat(1u);
return x_12;
}
}
else
{
lean_object* x_13; 
x_13 = lean_unsigned_to_nat(0u);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_LoVe_fib___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_LoVe_fib(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_LoVe_add(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_nat_dec_eq(x_2, x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_unsigned_to_nat(1u);
x_6 = lean_nat_sub(x_2, x_5);
x_7 = l_LoVe_add(x_1, x_6);
lean_dec(x_6);
x_8 = lean_nat_add(x_7, x_5);
lean_dec(x_7);
return x_8;
}
else
{
lean_inc(x_1);
return x_1;
}
}
}
LEAN_EXPORT lean_object* l_LoVe_add___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_LoVe_add(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_LoVe_mul(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_nat_dec_eq(x_2, x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_unsigned_to_nat(1u);
x_6 = lean_nat_sub(x_2, x_5);
x_7 = l_LoVe_mul(x_1, x_6);
lean_dec(x_6);
x_8 = l_LoVe_add(x_1, x_7);
lean_dec(x_7);
return x_8;
}
else
{
lean_object* x_9; 
x_9 = lean_unsigned_to_nat(0u);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_LoVe_mul___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_LoVe_mul(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_LoVe_power(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_nat_dec_eq(x_2, x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_unsigned_to_nat(1u);
x_6 = lean_nat_sub(x_2, x_5);
x_7 = l_LoVe_power(x_1, x_6);
lean_dec(x_6);
x_8 = l_LoVe_mul(x_1, x_7);
lean_dec(x_7);
return x_8;
}
else
{
lean_object* x_9; 
x_9 = lean_unsigned_to_nat(1u);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_LoVe_power___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_LoVe_power(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_LoVe_powerParam(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_nat_dec_eq(x_2, x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_unsigned_to_nat(1u);
x_6 = lean_nat_sub(x_2, x_5);
x_7 = l_LoVe_powerParam(x_1, x_6);
lean_dec(x_6);
x_8 = l_LoVe_mul(x_1, x_7);
lean_dec(x_7);
return x_8;
}
else
{
lean_object* x_9; 
x_9 = lean_unsigned_to_nat(1u);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_LoVe_powerParam___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_LoVe_powerParam(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_LoVe_iter___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_nat_dec_eq(x_3, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_nat_sub(x_3, x_6);
lean_inc(x_2);
x_8 = l_LoVe_iter___rarg(x_1, x_2, x_7);
lean_dec(x_7);
x_9 = lean_apply_1(x_2, x_8);
return x_9;
}
else
{
lean_dec(x_2);
lean_inc(x_1);
return x_1;
}
}
}
LEAN_EXPORT lean_object* l_LoVe_iter(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_LoVe_iter___rarg___boxed), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_LoVe_iter___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_LoVe_iter___rarg(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_LoVe_powerIter(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_alloc_closure((void*)(l_LoVe_mul___boxed), 2, 1);
lean_closure_set(x_3, 0, x_1);
x_4 = lean_unsigned_to_nat(1u);
x_5 = l_LoVe_iter___rarg(x_4, x_3, x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_LoVe_powerIter___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_LoVe_powerIter(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_LoVe_append___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_inc(x_2);
return x_2;
}
else
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_1, 1);
x_5 = l_LoVe_append___rarg(x_4, x_2);
lean_ctor_set(x_1, 1, x_5);
return x_1;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_1, 0);
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
lean_inc(x_6);
lean_dec(x_1);
x_8 = l_LoVe_append___rarg(x_7, x_2);
x_9 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_9, 0, x_6);
lean_ctor_set(x_9, 1, x_8);
return x_9;
}
}
}
}
LEAN_EXPORT lean_object* l_LoVe_append(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_LoVe_append___rarg___boxed), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_LoVe_append___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_LoVe_append___rarg(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_LoVe_appendImplicit___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_inc(x_2);
return x_2;
}
else
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_1, 1);
x_5 = l_LoVe_appendImplicit___rarg(x_4, x_2);
lean_ctor_set(x_1, 1, x_5);
return x_1;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_1, 0);
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
lean_inc(x_6);
lean_dec(x_1);
x_8 = l_LoVe_appendImplicit___rarg(x_7, x_2);
x_9 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_9, 0, x_6);
lean_ctor_set(x_9, 1, x_8);
return x_9;
}
}
}
}
LEAN_EXPORT lean_object* l_LoVe_appendImplicit(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_LoVe_appendImplicit___rarg___boxed), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_LoVe_appendImplicit___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_LoVe_appendImplicit___rarg(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_LoVe_appendPretty___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_inc(x_2);
return x_2;
}
else
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_1, 1);
x_5 = l_LoVe_appendPretty___rarg(x_4, x_2);
lean_ctor_set(x_1, 1, x_5);
return x_1;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_1, 0);
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
lean_inc(x_6);
lean_dec(x_1);
x_8 = l_LoVe_appendPretty___rarg(x_7, x_2);
x_9 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_9, 0, x_6);
lean_ctor_set(x_9, 1, x_8);
return x_9;
}
}
}
}
LEAN_EXPORT lean_object* l_LoVe_appendPretty(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_LoVe_appendPretty___rarg___boxed), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_LoVe_appendPretty___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_LoVe_appendPretty___rarg(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_LoVe_reverse___rarg(lean_object* x_1) {
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
x_4 = lean_ctor_get(x_1, 1);
x_5 = l_LoVe_reverse___rarg(x_4);
x_6 = lean_box(0);
lean_ctor_set(x_1, 1, x_6);
x_7 = l_List_appendTR___rarg(x_5, x_1);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_8 = lean_ctor_get(x_1, 0);
x_9 = lean_ctor_get(x_1, 1);
lean_inc(x_9);
lean_inc(x_8);
lean_dec(x_1);
x_10 = l_LoVe_reverse___rarg(x_9);
x_11 = lean_box(0);
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_8);
lean_ctor_set(x_12, 1, x_11);
x_13 = l_List_appendTR___rarg(x_10, x_12);
return x_13;
}
}
}
}
LEAN_EXPORT lean_object* l_LoVe_reverse(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_LoVe_reverse___rarg), 1, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_LoVe_eval(lean_object* x_1, lean_object* x_2) {
_start:
{
switch (lean_obj_tag(x_2)) {
case 0:
{
lean_object* x_3; 
lean_dec(x_1);
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
lean_dec(x_2);
return x_3;
}
case 1:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
lean_dec(x_2);
x_5 = lean_apply_1(x_1, x_4);
return x_5;
}
case 2:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_6 = lean_ctor_get(x_2, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_2, 1);
lean_inc(x_7);
lean_dec(x_2);
lean_inc(x_1);
x_8 = l_LoVe_eval(x_1, x_6);
x_9 = l_LoVe_eval(x_1, x_7);
x_10 = lean_int_add(x_8, x_9);
lean_dec(x_9);
lean_dec(x_8);
return x_10;
}
case 3:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_11 = lean_ctor_get(x_2, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_2, 1);
lean_inc(x_12);
lean_dec(x_2);
lean_inc(x_1);
x_13 = l_LoVe_eval(x_1, x_11);
x_14 = l_LoVe_eval(x_1, x_12);
x_15 = lean_int_sub(x_13, x_14);
lean_dec(x_14);
lean_dec(x_13);
return x_15;
}
case 4:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_16 = lean_ctor_get(x_2, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_2, 1);
lean_inc(x_17);
lean_dec(x_2);
lean_inc(x_1);
x_18 = l_LoVe_eval(x_1, x_16);
x_19 = l_LoVe_eval(x_1, x_17);
x_20 = lean_int_mul(x_18, x_19);
lean_dec(x_19);
lean_dec(x_18);
return x_20;
}
default: 
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_21 = lean_ctor_get(x_2, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_2, 1);
lean_inc(x_22);
lean_dec(x_2);
lean_inc(x_1);
x_23 = l_LoVe_eval(x_1, x_21);
x_24 = l_LoVe_eval(x_1, x_22);
x_25 = l_Int_ediv(x_23, x_24);
lean_dec(x_24);
lean_dec(x_23);
return x_25;
}
}
}
}
static lean_object* _init_l_LoVe_SorryTheorems_a___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_LoVe_SorryTheorems_a() {
_start:
{
lean_object* x_1; 
x_1 = l_LoVe_SorryTheorems_a___closed__1;
return x_1;
}
}
static lean_object* _init_l_LoVe_SorryTheorems_b() {
_start:
{
lean_object* x_1; 
x_1 = l_LoVe_SorryTheorems_a___closed__1;
return x_1;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_LoVe_LoVelib(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_LoVe_LoVe02__ProgramsAndTheorems__Demo(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_LoVe_LoVelib(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_LoVe_SorryTheorems_a___closed__1 = _init_l_LoVe_SorryTheorems_a___closed__1();
lean_mark_persistent(l_LoVe_SorryTheorems_a___closed__1);
l_LoVe_SorryTheorems_a = _init_l_LoVe_SorryTheorems_a();
lean_mark_persistent(l_LoVe_SorryTheorems_a);
l_LoVe_SorryTheorems_b = _init_l_LoVe_SorryTheorems_b();
lean_mark_persistent(l_LoVe_SorryTheorems_b);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
