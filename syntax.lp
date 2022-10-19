/* TODO add header */
// TODO fix infix precedence

// Identifiers
constant symbol ID : TYPE;

constant symbol aa : TYPE;

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
constant symbol Set : T → T;
constant symbol * : T → T → T;
notation * infix 1;
constant symbol make_pair [t1 t2] : τ t1 → τ t2 → τ (t1 * t2);
symbol proj_l [t1 t2] : τ (t1 * t2) → τ t1;
symbol proj_r [t1 t2] : τ (t1 * t2) → τ t2;

rule proj_l (make_pair $a _) ↪ $a;
rule proj_r (make_pair _ $b) ↪ $b;

// Structures
// Note that the order of declaration is relevant in Atelier B, i.e. struct(a : A, b : B) ≠ struct (b : B, a : A)
// I do not check that all record labels are different (is this a problem?)
constant symbol struct_sig : TYPE;
constant symbol struct_nil (i : ID) (t : T) : struct_sig;
constant symbol struct_cons (i : ID) (t : T) (cdr : struct_sig) : struct_sig;
constant symbol struct_T : struct_sig → T;

constant symbol accessible : ID → T → struct_sig → TYPE;
constant symbol accessible_nil id t : accessible id t (struct_nil id t);
constant symbol accessible_cons id t s : accessible id t (struct_cons id t s);
constant symbol skip id1 t1 id2 t2 s : accessible id1 t1 s → accessible id1 t1 (struct_cons id2 t2 s);

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
constant symbol ∈ [t] : τ t → τ (Set t) → U;
notation ∈ infix 2;
symbol notin [t] (x : τ t) y ≔ ¬ (x ∈ y);
notation notin infix 1;

// Inclusion
symbol ⊆ [t] (x y : τ (Set t)) ≔ (`∀ e, e ∈ x ⇒ e ∈ y);
notation ⊆ infix 2;
symbol ⊂ [t] (x y : τ (Set t)) ≔ x ⊆ y ∧ x ≠ y;
notation ⊂ infix 2;
symbol notsubseteq [t] (x y : τ (Set t)) ≔ ¬ (x ⊆ y);
notation notsubseteq infix 2;
symbol notsubset [t] (x y : τ (Set t)) ≔ ¬ (x ⊂ y);
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
constant symbol succ : τ (Set (Z_T * Z_T));
constant symbol pred : τ (Set (Z_T * Z_T));
// floor, ceiling and real are not of this type in the implementation, but they are in the documentation
constant symbol floor : τ (Set (R_T * Z_T));
constant symbol ceiling : τ (Set (R_T * Z_T));
constant symbol real : τ (Set (Z_T * R_T));

// Other arithmetic
constant symbol max : τ (Set Z_T) → τ Z_T;
constant symbol min : τ (Set Z_T) → τ Z_T;
constant symbol card [t] : τ (Set t) → τ Z_T;

// TODO add generalized sums and generalized products

// Couples
constant symbol ↦ [t1 t2] : τ t1 → τ t2 → τ (t1 * t2);
notation ↦ infix 2;

// Sets
// Set constructors
constant symbol specify [t] : (τ t → U) → τ (Set t);
constant symbol choice [t] : (τ (Set t)) → τ t;
symbol P [t] (x : τ (Set t)) ≔ specify (λ y, (y ⊆ x));
// TODO maybe define finite extensionality, and give a definition of finite subsets ?
constant symbol F [t] : τ (Set t) → τ (Set (Set t));
symbol × [t1 t2] (x : τ (Set t1)) (y : τ (Set t2)) ≔ specify (λ z, proj_l z ∈ x ∧ proj_r z ∈ y);
notation × infix 2;
symbol ∅ [t] : τ (Set t) ≔ specify (λ x, x ≠ x);
symbol P1 [t] (x : τ (Set t)) ≔ specify (λ f : τ (Set t), (f ∈ P x) ∧ (f ≠ ∅));
symbol F1 [t] (x : τ (Set t)) ≔ specify (λ f : τ (Set t), (f ∈ F x) ∧ (f ≠ ∅));
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
symbol STRING ≔ specify [STRING_T] (λ x, x = x);

// Set operations
symbol -_Set [t] (x y : τ (Set t)) ≔ specify (λ z, z ∈ x ∧ (z notin y));
notation -_Set infix 2;
symbol ∪ [t] (x y : τ (Set t)) ≔ specify (λ z, z ∈ x ∨ z ∈ y);
notation ∪ infix 2;
symbol ∩ [t] (x y : τ (Set t)) ≔ specify (λ z, z ∈ x ∧ z ∈ y);
notation ∩ infix 2;
symbol union [t] (x : τ (Set (Set t))) ≔ specify (λ z, `∃ y, z ∈ y ∧ y ∈ x);
symbol inter [t] (x : τ (Set (Set t))) ≔ specify (λ z, `∀ y, (y ∈ x ⇒ z ∈ y));
// TODO quantified union and intersection

// Records
constant symbol rec_nil [t] (id : ID) (x : τ t) : τ (struct_T (struct_nil id t));
constant symbol rec_cons [t1 t2] (id : ID) (x : τ t1) (cdr : τ (struct_T t2)) : τ (struct_T (struct_cons id t1 t2));
// Accessor
constant symbol ' [t1 t2] (x : τ (struct_T t1)) id : accessible id t2 t1 → τ t2;
notation ' infix 2;

// Set of relations
symbol ↔ [t1 t2] (x : τ (Set t1)) (y : τ (Set t2)) ≔ P (x × y);
notation ↔ infix 2;

// Relations
symbol id [t] ≔ specify (λ x : τ (t * t), proj_l x = proj_r x);
symbol inverse [t1 t2] (r : τ (Set (t1 * t2))) ≔ specify (λ x, make_pair (proj_r x) (proj_l x) ∈ r);
symbol prj1 [t1 t2] (x : τ (Set t1)) (y : τ (Set t2)) ≔ specify (λ z : τ ((t1 * t2) * t1), z ∈ ((x × y) × x) ∧ (proj_l (proj_l z)) = proj_r z);
symbol prj2 [t1 t2] (x : τ (Set t1)) (y : τ (Set t2)) ≔ specify (λ z : τ ((t1 * t2) * t2), z ∈ ((x × y) × y) ∧ (proj_r (proj_l z)) = proj_r z);
symbol ∘ [t u v] (r1 : τ (Set (t * u))) (r2 : τ (Set (u * v))) ≔ specify (λ x, `∃ y, (make_pair (proj_l x) y ∈ r1) ∧ (make_pair y (proj_r x) ∈ r2));
notation ∘ infix 2;
symbol ⊗ [t u v] (r1 : τ (Set (t * u))) (r2 : τ (Set (t * v))) ≔ specify (λ x, (make_pair (proj_l x) (proj_l (proj_r x)) ∈ r1) ∧ (make_pair (proj_l x) (proj_r (proj_r x)) ∈ r2));
notation ⊗ infix 2;
symbol ∥ [t u v w] (r1 : τ (Set (t * u))) (r2 : τ (Set (v * w))) ≔ specify (λ x, (make_pair (proj_l (proj_l x)) (proj_l (proj_r x)) ∈ r1) ∧ (make_pair (proj_r (proj_l x)) (proj_r (proj_r x)) ∈ r2));
notation ∥ infix 2;

// Iterations of relations
constant symbol iter [t] : τ (Set (t * t)) → τ Z_T → τ (Set (t * t));
constant symbol star [t] : τ (Set (t * t)) → τ (Set (t * t));
constant symbol plus [t] : τ (Set (t * t)) → τ (Set (t * t));

symbol dom [t1 t2] (r : τ (Set (t1 * t2))) ≔ specify (λ x, `∃ y, make_pair x y ∈ r);
symbol ran [t1 t2] (r : τ (Set (t1 * t2))) ≔ specify (λ x, `∃ y, make_pair y x ∈ r);
symbol image_r [t1 t2] (r : τ (Set (t1 * t2))) (e : τ (Set t1)) ≔ specify (λ x, `∃ y, y ∈ e ∧ make_pair y x ∈ r);

// Changing relations
symbol ◁ [t1 t2] (e : τ (Set t1)) (r : τ (Set (t1 * t2)))  ≔ specify (λ x, proj_l x ∈ e ∧ x ∈ r);
notation ◁ infix 2;
symbol ◁- [t1 t2] (e : τ (Set t1)) (r : τ (Set (t1 * t2))) ≔ specify (λ x, ((proj_l x) notin e) ∧ x ∈ r);
notation ◁- infix 2;
symbol ▷ [t1 t2] (r : τ (Set (t1 * t2))) (e : τ (Set t2)) ≔ specify (λ x, proj_r x ∈ e ∧ x ∈ r);
notation ▷ infix 2;
symbol ▷- [t1 t2] (r : τ (Set (t1 * t2))) (e : τ (Set t2)) ≔ specify (λ x, ((proj_r x) notin e) ∧ x ∈ r);
notation ▷- infix 2;
symbol overwrite [t1 t2] (r1 r2 : τ (Set (t1 * t2))) ≔ specify (λ x, (x ∈ r1 ∧ ((proj_l x) notin (dom r2))) ∨ x ∈ r2);

// Function sets
symbol +> [t1 t2] (e1 : τ (Set t1)) (e2 : τ (Set t2)) ≔ specify (λ x, x ∈ (e1 ↔ e2) ∧ ((inverse x) ∘ x) ⊆ id);
notation +> infix 2;
symbol -> [t1 t2] (e1 : τ (Set t1)) (e2 : τ (Set t2)) ≔ specify (λ x, x ∈ (e1 +> e2) ∧ dom x = e1);
notation -> infix 2;
symbol >+> [t1 t2] (e1 : τ (Set t1)) (e2 : τ (Set t2)) ≔ specify (λ x, x ∈ (e1 +> e2) ∧ (inverse x) ∈ (e2 +> e1));
notation >+> infix 2;
symbol >-> [t1 t2] (e1 : τ (Set t1)) (e2 : τ (Set t2)) ≔ (e1 >+> e2) ∩ (e1 -> e2);
notation >-> infix 2;
symbol +>> [t1 t2] (e1 : τ (Set t1)) (e2 : τ (Set t2)) ≔ specify (λ x, x ∈ (e1 +> e2) ∧ ran x = e2);
notation +>> infix 2;
symbol ->> [t1 t2] (e1 : τ (Set t1)) (e2 : τ (Set t2)) ≔ (e1 +>> e2) ∩ (e1 -> e2);
notation ->> infix 2;
symbol >->> [t1 t2] (e1 : τ (Set t1)) (e2 : τ (Set t2)) ≔ (e1 >-> e2) ∩ (e1 ->> e2);
notation >->> infix 2;

// Functions
symbol fun [t1 t2] (P : τ t1 → U) (f : τ t1 → τ t2) ≔ specify (λ x, P (proj_l x) ∧ proj_r x = f (proj_l x));
symbol ⋅ [t1 t2] (f : τ (Set (t1 * t2))) (x : τ t1) : τ t2 ≔ choice (specify (λ y, make_pair x y ∈ f));
notation ⋅ infix 2;
symbol fnc [t1 t2] (r : τ (Set (t1 * t2))) ≔ fun (λ x, x = x) (λ x, specify (λ y, make_pair x y ∈ r));
symbol rel [t1 t2] (f : τ (Set (t1 * (Set t2)))) ≔ specify (λ x, `∃ y, proj_r x ∈ y ∧ make_pair (proj_l x) y ∈ f);

// Sequences
symbol seq [t] (E : τ (Set t)) ≔ specify (λ f, `∃ n, n ∈ N ∧ f ∈ ((1 -- n) -> E));
symbol seq1 [t] (E : τ (Set t)) ≔ specify (λ f, `∃ n, n ∈ N1 ∧ f ∈ ((1 -- n) -> E));
symbol iseq [t] (E : τ (Set t)) ≔ specify (λ f, f ∈ seq E ∧ f ∈ (N1 >+> E));
symbol iseq1 [t] (E : τ (Set t)) ≔ specify (λ f, f ∈ seq1 E ∧ f ∈ (N1 >+> E));
symbol perm [t] (E : τ (Set t)) ≔ specify (λ f, f ∈ iseq E ∧ f ∈ (N1 +>> E));
// TODO sequence constructors

symbol size [t] (s : τ (Set (Z_T * t))) ≔ card s;
symbol first [t] (s : τ (Set (Z_T * t))) ≔ s ⋅ 1;
symbol last [t] (s : τ (Set (Z_T * t))) ≔ s ⋅ (size s);

symbol ↑ [t] (s : τ (Set (Z_T * t))) n ≔ (1 -- n) ◁ s;
notation ↑ infix 2;
symbol ↓ [t] (s : τ (Set (Z_T * t))) n ≔ fun (λ i, i ∈ (1 -- ((size s) -_Z n))) (λ i, s ⋅ (n +_Z i));
notation ↓ infix 2;

symbol front [t] (s : τ (Set (Z_T * t))) ≔ s ↑ (size s -_Z 1);
symbol tail [t] (s : τ (Set (Z_T * t))) ≔ s ↓ 1;
symbol rev [t] (s : τ (Set (Z_T * t))) ≔ fun (λ i, i ∈ (1 -- size s)) (λ i, s ⋅ ((size s -_Z i) +_Z 1));

symbol concat [t] (s1 : τ (Set (Z_T * t))) (s2 : τ (Set (Z_T * t))) ≔ s1 ∪ (fun (λ i, i ∈ (((size s1) +_Z 1) -- (size(s1) +_Z (size s2)))) (λ i, s2 ⋅ (i -_Z (size s1))));
