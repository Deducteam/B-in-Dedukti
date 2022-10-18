/* TODO add header */
// TODO fix infix precedence

// Identifiers
constant symbol ID : TYPE;

/** B Types */
constant symbol T : TYPE;
constant symbol τ : T → TYPE;

// Base types
constant symbol Z_T : T;
constant symbol R_T : T;
constant symbol FLOAT_T : T;
constant symbol BOOL_T : T;
constant symbol STRING_T : T;

// Formal types
constant symbol type_T : ID → T;

// Type constructors
constant symbol P_T : T → T;
constant symbol ×_T : T → T → T;
notation ×_T infix 1;

// Structures
constant symbol struct_sig : TYPE;
constant symbol struct_nil (i : ID) (t : T) : struct_sig;
constant symbol struct_cons (i : ID) (t : T) (cdr : struct_sig) : struct_sig;
constant symbol struct_T : struct_sig → T;

/* Predicates */
constant symbol U : TYPE;
constant symbol Thm : U → TYPE;

// Propositional logic
constant symbol ⇒ : U → U → U;
notation ⇒ infix 1;
constant symbol ¬ : U → U;
symbol ∧ x y ≔ ¬ (x ⇒ ¬ y);
notation ∧ infix 1;
symbol ∨ x y ≔ ¬ x ⇒ y;
notation ∨ infix 1;
symbol ⇔ x y ≔ (x ⇒ y) ∧ (y ⇒ x);

// Quantifiers
constant symbol ∀ [t] : (τ t → U) → U;
notation ∀ quantifier;
symbol ∃ [t] (f : τ t → U) ≔ ¬ (`∀ x, ¬ (f x));
notation ∃ quantifier;

// Equality
constant symbol = [t] : τ t → τ t → U;
notation = infix 2;
symbol ≠ [t] (x y : τ t) ≔ ¬ (x = y);
notation ≠ infix 2;

// Belonging
constant symbol ∈ [t] : τ t → τ (P_T t) → U;
notation ∈ infix 2;
symbol notin [t] (x : τ t) y ≔ ¬ (x ∈ y);
notation notin infix 1;

// Inclusion
symbol ⊆ [t] (x y : τ (P_T t)) ≔ (`∀ e, e ∈ x ⇒ e ∈ y);
notation ⊆ infix 2;
symbol ⊂ [t] (x y : τ (P_T t)) ≔ x ⊆ y ∧ x ≠ y;
notation ⊂ infix 2;
symbol notsubseteq [t] (x y : τ (P_T t)) ≔ ¬ (x ⊆ y);
notation notsubseteq infix 2;
symbol notsubset [t] (x y : τ (P_T t)) ≔ ¬ (x ⊂ y);
notation notsubset infix 2;

// Comparisons for Z
constant symbol ≤_Z : τ Z_T → τ Z_T → U;
notation ≤_Z infix 2;
symbol <_Z x y ≔ x ≤_Z y ∧ x ≠ y;
notation <_Z infix 2;
symbol ≥_Z x y ≔ y ≤_Z x;
notation ≥_Z infix 2;
symbol >_Z x y ≔ y <_Z x;
notation >_Z infix 2;

// Comparisons for R
constant symbol ≤_R : τ Z_T → τ Z_T → U;
notation ≤_R infix 2;
symbol <_R x y ≔ x ≤_R y ∧ x ≠ y;
notation <_R infix 2;
symbol ≥_R x y ≔ y ≤_R x;
notation ≥_R infix 2;
symbol >_R x y ≔ y <_R x;
notation >_R infix 2;

// Comparisons for FLOAT
constant symbol ≤_FLOAT : τ Z_T → τ Z_T → U;
notation ≤_FLOAT infix 2;
symbol <_FLOAT x y ≔ x ≤_FLOAT y ∧ x ≠ y;
notation <_FLOAT infix 2;
symbol ≥_FLOAT x y ≔ y ≤_FLOAT x;
notation ≥_FLOAT infix 2;
symbol >_FLOAT x y ≔ y <_FLOAT x;
notation >_FLOAT infix 2;

/* Expressions */
// TODO what is $0 and renaming data?

// TODO data definitions: strings, integers, and reals (and floats?)
constant symbol 0 : τ Z_T;
constant symbol 1 : τ Z_T;

// Booleans
constant symbol TRUE : τ BOOL_T;
constant symbol FALSE : τ BOOL_T;
constant symbol bool : U → τ BOOL_T;

// Arithmetic for Z
constant symbol MAXINT : τ Z_T;
constant symbol MININT : τ Z_T;
constant symbol +_Z : τ Z_T → τ Z_T → τ Z_T;
notation +_Z infix 2;
constant symbol -_Z : τ Z_T → τ Z_T → τ Z_T;
notation -_Z infix 2;
constant symbol neg_Z : τ Z_T → τ Z_T;
constant symbol *_Z : τ Z_T → τ Z_T → τ Z_T;
notation *_Z infix 2;
constant symbol div_Z : τ Z_T → τ Z_T → τ Z_T;
notation div_Z infix 2;
constant symbol mod : τ Z_T → τ Z_T → τ Z_T;
constant symbol ** : τ Z_T → τ Z_T → τ Z_T;
notation ** infix 2;

// Arithmetic for R
constant symbol +_R : τ R_T → τ R_T → τ R_T;
notation +_R infix 2;
constant symbol -_R : τ R_T → τ R_T → τ R_T;
notation -_R infix 2;
constant symbol neg_R : τ R_T → τ R_T;
constant symbol *_R : τ R_T → τ R_T → τ R_T;
notation *_R infix 2;
constant symbol div_R : τ R_T → τ R_T → τ R_T;
notation div_R infix 2;

// Arithmetic for FLOAT
constant symbol +_FLOAT : τ FLOAT_T → τ FLOAT_T → τ FLOAT_T;
notation +_FLOAT infix 2;
constant symbol -_FLOAT : τ FLOAT_T → τ FLOAT_T → τ FLOAT_T;
notation -_FLOAT infix 2;
constant symbol neg_FLOAT : τ FLOAT_T → τ FLOAT_T;
constant symbol *_FLOAT : τ FLOAT_T → τ FLOAT_T → τ FLOAT_T;
notation *_FLOAT infix 2;
constant symbol div_FLOAT : τ FLOAT_T → τ FLOAT_T → τ FLOAT_T;
notation div_FLOAT infix 2;

// Arithmetic functions with complex types
constant symbol succ : τ (P_T (Z_T ×_T Z_T));
constant symbol pred : τ (P_T (Z_T ×_T Z_T));
// floor, ceiling and real are not of this type in the implementation, but they are in the documentation
constant symbol floor : τ (P_T (R_T ×_T Z_T));
constant symbol ceiling : τ (P_T (R_T ×_T Z_T));
constant symbol real : τ (P_T (Z_T ×_T R_T));

// Other arithmetic
constant symbol max : τ (P_T Z_T) → τ Z_T;
constant symbol min : τ (P_T Z_T) → τ Z_T;
constant symbol card [t] : τ (P_T t) → τ Z_T;

// TODO add generalized sums and generalized products

// Couples
constant symbol ↦ [t1 t2] : τ t1 → τ t2 → τ (t1 ×_T t2);
notation ↦ infix 2;

// Sets
// Set constructors
constant symbol specify [t] : (τ t → U) → τ (P_T t);
symbol P [t] (x : τ (P_T t)) ≔ specify (λ y, (y ⊆ x));
// TODO maybe define finite extensionality, and give a definition of finite subsets ?
constant symbol F [t] : τ (P_T t) → τ (P_T (P_T t));
constant symbol × [t1 t2] : τ (P_T t1) → τ (P_T t2) → τ ((P_T t1) ×_T (P_T t2));
symbol ∅ [t] : τ (P_T t) ≔ specify (λ x, x ≠ x);
symbol P1 [t] (x : τ (P_T t)) ≔ specify (λ f : τ (P_T t), (f ∈ P x) ∧ (f ≠ ∅));
symbol F1 [t] (x : τ (P_T t)) ≔ specify (λ f : τ (P_T t), (f ∈ F x) ∧ (f ≠ ∅));
symbol -- x y ≔ specify (λ z, x ≤_Z z ∧ z ≤_Z y);
notation -- infix 2;

symbol Z ≔ specify [Z_T] (λ x, x = x);
symbol N ≔ specify (λ x, 0 ≤_Z x);
symbol N1 ≔ specify (λ x, 1 ≤_Z x);
symbol NAT ≔ 0 -- MAXINT;
symbol NAT1 ≔ 1 -- MAXINT;
symbol INT ≔ MININT -- MAXINT;
symbol R ≔ specify [R_T] (λ x, x = x);
symbol FLOAT ≔ specify [FLOAT_T] (λ x, x = x);
symbol BOOL ≔ specify [BOOL_T] (λ x, x = x);
symbol STRING ≔ specify [FLOAT_T] (λ x, x = x);

// Records
constant symbol rec_nil [t] (id : ID) (x : τ t) : τ (struct_T (struct_nil id t));
constant symbol rec_cons [t1 t2] (id : ID) (x : τ t1) (cdr : τ (struct_T t2)) : τ (struct_T (struct_cons id t1 t2));
