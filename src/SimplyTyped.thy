theory SimplyTyped
imports Main Permutation Fresh
begin

type_synonym tvar = nat

datatype type =
  TVar tvar
| TArr type type

datatype 'a pretrm =
  PVar 'a
| PApp "'a pretrm" "'a pretrm"
| PFn 'a type "'a pretrm"

print_theorems

fun PFV :: "'a pretrm \<Rightarrow> 'a set" where
  "PFV (PVar x) = {x}"
| "PFV (PApp A B) = PFV A \<union> PFV B"
| "PFV (PFn x _ A) = PFV A - {x}"

fun pretrm_apply_prm :: "'a prm \<Rightarrow> 'a pretrm \<Rightarrow> 'a pretrm" (infixr "\<cdot>" 150) where
  "pretrm_apply_prm \<pi> (PVar x) = PVar (\<pi> $ x)"
| "pretrm_apply_prm \<pi> (PApp A B) = PApp (pretrm_apply_prm \<pi> A) (pretrm_apply_prm \<pi> B)"
| "pretrm_apply_prm \<pi> (PFn x T A) = PFn (\<pi> $ x) T (pretrm_apply_prm \<pi> A)"

inductive pretrm_alpha_equiv :: "'a pretrm \<Rightarrow> 'a pretrm \<Rightarrow> bool" (infix "=a" 100) where
  var:        "(PVar x) =a (PVar x)"
| app:        "\<lbrakk>A =a B; C =a D\<rbrakk> \<Longrightarrow> (PApp A C) =a (PApp B D)"
| fn1:        "A =a B \<Longrightarrow> (PFn x T A) =a (PFn x T B)"
| fn2:        "\<lbrakk>a \<noteq> b; A =a [a \<leftrightarrow> b] \<cdot> B; a \<notin> PFV B\<rbrakk> \<Longrightarrow> (PFn a T A) =a (PFn b T B)"

inductive_cases varE: "PVar x =a Y"
inductive_cases appE: "PApp A B =a Y"
inductive_cases fnE:  "PFn x T A =a Y"

fun pretrm_size :: "'a pretrm \<Rightarrow> nat" where
  "pretrm_size (PVar _) = 1"
| "pretrm_size (PApp A B) = pretrm_size A + pretrm_size B + 1"
| "pretrm_size (PFn x T A) = pretrm_size A + 1"

lemma pretrm_size_nonzero:
  shows "pretrm_size M \<noteq> 0"
by(cases M, simp_all)

lemma pretrm_size_app1:
  shows "pretrm_size A < pretrm_size (PApp A B)"
by(induction A, simp_all)

lemma pretrm_size_app2:
  shows "pretrm_size B < pretrm_size (PApp A B)"
by(induction B, simp_all)

lemma pretrm_size_fn:
  shows "pretrm_size A < pretrm_size (PFn x T A)"
by(induction A, simp_all)

lemma pretrm_size_prm:
  shows "pretrm_size (\<pi> \<cdot> A) = pretrm_size A"
by(induction A, simp_all)

lemma pretrm_size_alpha_equiv:
  assumes "X =a Y"
  shows "pretrm_size X = pretrm_size Y"
using assms by(induction rule: pretrm_alpha_equiv.induct, simp_all add: pretrm_size_prm)

lemma pretrm_prm_apply_id:
  shows "\<epsilon> \<cdot> X = X"
by(induction X, simp_all add: prm_apply_id)

lemma pretrm_prm_apply_compose:
  shows "\<pi> \<cdot> \<sigma> \<cdot> X = (\<pi> \<circ> \<sigma>) \<cdot> X"
by(induction X, simp_all add: prm_apply_composition)

lemma pretrm_fvs_finite:
  shows "finite (PFV X)"
by(induction X, auto)

lemma pretrm_prm_fvs:
  shows "PFV (\<pi> \<cdot> X) = \<pi> {$} PFV X"
proof(induction X)
  case (PVar x)
    have "PFV (\<pi> \<cdot> PVar x) = PFV (PVar (\<pi> $ x))" by simp
    moreover have "... = {\<pi> $ x}" by simp
    moreover have "... = \<pi> {$} {x}" using prm_set_singleton by metis
    moreover have "... = \<pi> {$} PFV (PVar x)" by simp
    ultimately show ?case by metis
  next
  case (PApp A B)
    have "PFV (\<pi> \<cdot> PApp A B) = PFV (PApp (\<pi> \<cdot> A) (\<pi> \<cdot> B))" by simp
    moreover have "... = PFV (\<pi> \<cdot> A) \<union> PFV (\<pi> \<cdot> B)" by simp
    moreover have "... = \<pi> {$} PFV A \<union> \<pi> {$} PFV B" using PApp.IH by metis
    moreover have "... = \<pi> {$} (PFV A \<union> PFV B)" using prm_set_distributes_union by metis
    moreover have "... = \<pi> {$} PFV (PApp A B)" by simp
    ultimately show ?case by metis
  next
  case (PFn x T A)
    have "PFV (\<pi> \<cdot> PFn x T A) = PFV (PFn (\<pi> $ x) T (\<pi> \<cdot> A))" by simp
    moreover have "... = PFV (\<pi> \<cdot> A) - {\<pi> $ x}" by simp
    moreover have "... = \<pi> {$} PFV A - {\<pi> $ x}" using PFn.IH by metis
    moreover have "... = \<pi> {$} PFV A - \<pi> {$} {x}" using prm_set_singleton by metis
    moreover have "... = \<pi> {$} (PFV A - {x})" using prm_set_distributes_difference by metis
    moreover have "... = \<pi> {$} PFV (PFn x T A)" by simp
    ultimately show ?case by metis
  next
qed

lemma pretrm_alpha_equiv_fvs:
  assumes "X =a Y"
  shows "PFV X = PFV Y"
using assms proof(induction rule: pretrm_alpha_equiv.induct, simp, simp, simp)
  case (fn2 a b A B T)
    have "PFV (PFn a T A) = PFV A - {a}" by simp
    moreover have "... = PFV ([a \<leftrightarrow> b] \<cdot> B) - {a}" using fn2.IH by metis
    moreover have "... = ([a \<leftrightarrow> b] {$} PFV B) - {a}" using pretrm_prm_fvs by metis
    moreover have "... = PFV B - {b}"  proof -
      consider "b \<in> PFV B" | "b \<notin> PFV B" by auto
      thus ?thesis proof(cases)
        case 1
          thm prm_set_unit_action[where ?S = "PFV B" and ?a = b and ?b = a]
          have "[a \<leftrightarrow> b] {$} PFV B - {a} = [b \<leftrightarrow> a] {$} PFV B - {a}" using prm_unit_commutes by metis
          moreover have "... = ((PFV B - {b}) \<union> {a}) - {a}"
            using prm_set_unit_action `b \<in> PFV B` `a \<notin> PFV B` by metis
          moreover have "... = PFV B - {b}" using `a \<notin> PFV B` `a \<noteq> b`
            using Diff_insert0 Diff_insert2 Un_insert_right insert_Diff1 insert_is_Un singletonI
              sup_bot.right_neutral by blast (* why?! *)
          ultimately show ?thesis by metis
        next
        case 2
          hence "[a \<leftrightarrow> b] {$} PFV B - {a} = PFV B - {a}"
            using prm_set_unit_inaction `a \<notin> PFV B` by metis
          moreover have "... = PFV B" using `a \<notin> PFV B` by simp
          moreover have "... = PFV B - {b}" using `b \<notin> PFV B` by simp
          ultimately show ?thesis by metis
        next
      qed
    qed
    moreover have "... = PFV (PFn b T B)" by simp
    ultimately show ?case by metis
  next
qed

lemma pretrm_alpha_equiv_prm:
  assumes "X =a Y"
  shows "\<pi> \<cdot> X =a \<pi> \<cdot> Y"
sorry 

lemma pretrm_swp_transfer:
  assumes "[a \<leftrightarrow> b] \<cdot> X =a Y"
  shows "X =a [a \<leftrightarrow> b] \<cdot> Y"
proof -
  have "[a \<leftrightarrow> b] \<cdot> [a \<leftrightarrow> b] \<cdot> X =a [a \<leftrightarrow> b] \<cdot> Y"
    using assms pretrm_alpha_equiv_prm by metis
  hence "([a \<leftrightarrow> b] \<circ> [a \<leftrightarrow> b]) \<cdot> X =a [a \<leftrightarrow> b] \<cdot> Y" using pretrm_prm_apply_compose
    by metis
  hence "\<epsilon> \<cdot> X =a [a \<leftrightarrow> b] \<cdot> Y" using prm_unit_involution by metis
  thus ?thesis using pretrm_prm_apply_id by metis
qed

lemma pretrm_alpha_equiv_fvs_transfer:
  assumes "A =a [a \<leftrightarrow> b] \<cdot> B" and "a \<notin> PFV B" and "a \<noteq> b"
  shows "b \<notin> PFV A"
proof(cases "b \<in> PFV B")
  case True
    have *: "b \<notin> PFV B - {b} \<union> {a}" using assms by simp
    have "PFV A = PFV ([a \<leftrightarrow> b] \<cdot> B)" using pretrm_alpha_equiv_fvs assms by metis
    moreover have "... = [a \<leftrightarrow> b] {$} PFV B" using pretrm_prm_fvs by metis
    moreover have "... = [b \<leftrightarrow> a] {$} PFV B" using prm_unit_commutes by metis
    moreover have "... = PFV B - {b} \<union> {a}" using prm_set_unit_action `a \<notin> PFV B` `b \<in> PFV B` by metis
    ultimately have "PFV A = PFV B - {b} \<union> {a}" by metis
    thus ?thesis using * by auto
  next
  case False
    have "PFV A = PFV ([a \<leftrightarrow> b] \<cdot> B)" using pretrm_alpha_equiv_fvs assms by metis
    moreover have "PFV ([a \<leftrightarrow> b] \<cdot> B) = [a \<leftrightarrow> b] {$} PFV B" using pretrm_prm_fvs by metis
    moreover have "... = PFV B" using prm_set_unit_inaction `a \<notin> PFV B` `b \<notin> PFV B` by metis
    ultimately have "PFV A = PFV B" by metis
    thus ?thesis using `b \<notin> PFV B` by auto
  next
qed

lemma pretrm_prm_agreement_equiv:
  assumes "\<And>a. a \<in> prm_disagreement \<pi> \<sigma> \<Longrightarrow> a \<notin> PFV M"
  shows "\<pi> \<cdot> M =a \<sigma> \<cdot> M"
sorry

lemma pretrm_alpha_equiv_reflexive:
  shows "M =a M"
by(induction M, (metis pretrm_alpha_equiv.intros)+)

corollary pretrm_alpha_equiv_reflp:
  shows "reflp pretrm_alpha_equiv"
unfolding reflp_def using pretrm_alpha_equiv_reflexive by auto

lemma pretrm_alpha_equiv_symmetric:
  assumes "X =a Y"
  shows "Y =a X"
using assms proof(induction rule: pretrm_alpha_equiv.induct, (metis pretrm_alpha_equiv.intros)+)
  case (fn2 a b A B T)
    have "b \<noteq> a" using `a \<noteq> b` by auto
    have "B =a [b \<leftrightarrow> a] \<cdot> A" using `[a \<leftrightarrow> b] \<cdot> B =a A`
      using pretrm_swp_transfer prm_unit_commutes by metis

    have "b \<notin> PFV A" using `a \<notin> PFV B` `A =a [a \<leftrightarrow> b] \<cdot> B` `a \<noteq> b`
      using pretrm_alpha_equiv_fvs_transfer by metis

    show ?case using `b \<noteq> a` `B =a [b \<leftrightarrow> a] \<cdot> A` `b \<notin> PFV A`
      using pretrm_alpha_equiv.fn2 by metis
  next
qed

corollary pretrm_alpha_equiv_symp:
  shows "symp pretrm_alpha_equiv"
unfolding symp_def using pretrm_alpha_equiv_symmetric by auto

lemma pretrm_alpha_equiv_transitive:
  assumes "X =a Y" and "Y =a Z"
  shows "X =a Z"
using assms proof(induction "pretrm_size X" arbitrary: X Y Z rule: less_induct)
  fix X Y Z :: "'a pretrm"
  assume IH: "\<And>K Y Z :: 'a pretrm. pretrm_size K < pretrm_size X \<Longrightarrow> K =a Y \<Longrightarrow> Y =a Z \<Longrightarrow> K =a Z"
  assume "X =a Y" and "Y =a Z"
  show "X =a Z" proof(cases X)
    case (PVar x)
      hence "PVar x =a Y" using `X =a Y` by auto
      hence "Y = PVar x" using varE by metis
      hence "PVar x =a Z" using `Y =a Z` by auto
      hence "Z = PVar x" using varE by metis
      thus ?thesis using pretrm_alpha_equiv.var `X = PVar x` by metis
    next
    case (PApp A B)
      obtain C D where "Y = PApp C D" and "A =a C" and "B =a D"
        using appE `X = PApp A B` `X =a Y` by metis
      hence "PApp C D =a Z" using `Y =a Z` by simp
      from this obtain E F where "Z = PApp E F" and "C =a E" and "D =a F" using appE by metis

      have "pretrm_size A < pretrm_size X" and "pretrm_size B < pretrm_size X"
        using pretrm_size_app1 pretrm_size_app2 `X = PApp A B` by auto
      hence "A =a E" and "B =a F" using IH `A =a C` `C =a E` `B =a D` `D =a F` by auto
      thus ?thesis using `X = PApp A B` `Z = PApp E F` pretrm_alpha_equiv.app by metis
    next
    case (PFn x T A)
      from this have X: "X = PFn x T A".
      hence *: "pretrm_size A < pretrm_size X" using pretrm_size_fn by auto

      obtain y B where "Y = PFn y T B"
        and Y_cases: "(x = y \<and> A =a B) \<or> (x \<noteq> y \<and> A =a [x \<leftrightarrow> y] \<cdot> B \<and> x \<notin> PFV B)"
        using fnE `X =a Y` `X = PFn x T A` by metis
      obtain z C where Z: "Z = PFn z T C"
        and Z_cases: "(y = z \<and> B =a C) \<or> (y \<noteq> z \<and> B =a [y \<leftrightarrow> z] \<cdot> C \<and> y \<notin> PFV C)"
        using fnE `Y =a Z` `Y = PFn y T B` by metis

      consider
        "x = y" "A =a B" and "y = z" "B =a C"
      | "x = y" "A =a B" and "y \<noteq> z" "B =a [y \<leftrightarrow> z] \<cdot> C" "y \<notin> PFV C"
      | "x \<noteq> y" "A =a [x \<leftrightarrow> y] \<cdot> B" "x \<notin> PFV B" and "y = z" "B =a C"
      | "x \<noteq> y" "A =a [x \<leftrightarrow> y] \<cdot> B" "x \<notin> PFV B" and "y \<noteq> z" "B =a [y \<leftrightarrow> z] \<cdot> C" "y \<notin> PFV C" and "x = z"
      | "x \<noteq> y" "A =a [x \<leftrightarrow> y] \<cdot> B" "x \<notin> PFV B" and "y \<noteq> z" "B =a [y \<leftrightarrow> z] \<cdot> C" "y \<notin> PFV C" and "x \<noteq> z"
        using Y_cases Z_cases by auto

      thus ?thesis proof(cases)
        case 1
          have "A =a C" using `A =a B` `B =a C` IH * by metis
          have "x = z" using `x = y` `y = z` by metis
          show ?thesis using `A =a C` `x = z` X Z
            using pretrm_alpha_equiv.fn1 by metis
        next
        case 2
          have "x \<noteq> z" using `x = y` `y \<noteq> z` by metis
          have "A =a [x \<leftrightarrow> z] \<cdot> C" using `A =a B` `B =a [y \<leftrightarrow> z] \<cdot> C` `x = y` IH * by metis
          have "x \<notin> PFV C" using `x = y` `y \<notin> PFV C` by metis
          thus ?thesis using `x \<noteq> z` `A =a [x \<leftrightarrow> z] \<cdot> C` `x \<notin> PFV C` X Z
            using pretrm_alpha_equiv.fn2 by metis
        next
        case 3
          have "x \<noteq> z" using `x \<noteq> y` `y = z` by metis
          have "[x \<leftrightarrow> y] \<cdot> B =a [x \<leftrightarrow> y] \<cdot> C" using `B =a C` pretrm_alpha_equiv_prm by metis
          have "A =a [x \<leftrightarrow> z] \<cdot> C"
            using `A =a [x \<leftrightarrow> y] \<cdot> B` `[x \<leftrightarrow> y] \<cdot> B =a [x \<leftrightarrow> y] \<cdot> C` `y = z` IH *
            by metis
          have "x \<notin> PFV C" using `B =a C` `x \<notin> PFV B` pretrm_alpha_equiv_fvs by metis
          thus ?thesis using `x \<noteq> z` `A =a [x \<leftrightarrow> z] \<cdot> C` `x \<notin> PFV C` X Z
            using pretrm_alpha_equiv.fn2 by metis
        next
        case 4
          have "[x \<leftrightarrow> y] \<cdot> B =a [x \<leftrightarrow> y] \<cdot> [y \<leftrightarrow> z] \<cdot> C"
            using `B =a [y \<leftrightarrow> z] \<cdot> C` pretrm_alpha_equiv_prm by metis
          hence "A =a [x \<leftrightarrow> y] \<cdot> [y \<leftrightarrow> z] \<cdot> C"
            using `A =a [x \<leftrightarrow> y] \<cdot> B` IH * by metis
          hence "A =a ([x \<leftrightarrow> y] \<circ> [y \<leftrightarrow> z]) \<cdot> C" using pretrm_prm_apply_compose by metis
          hence "A =a ([x \<leftrightarrow> y] \<circ> [y \<leftrightarrow> x]) \<cdot> C" using `x = z` by metis
          hence "A =a ([x \<leftrightarrow> y] \<circ> [x \<leftrightarrow> y]) \<cdot> C" using prm_unit_commutes by metis
          hence "A =a \<epsilon> \<cdot> C" using `x = z` prm_unit_involution by metis
          hence "A =a C" using pretrm_prm_apply_id by metis

          thus ?thesis using `x = z` `A =a C` X Z
            using pretrm_alpha_equiv.fn1 by metis
        next
        case 5
          have "x \<notin> PFV C" proof -
            have "PFV B = PFV ([y \<leftrightarrow> z] \<cdot> C)"
              using pretrm_alpha_equiv_fvs `B =a [y \<leftrightarrow> z] \<cdot> C` by metis
            hence "x \<notin> PFV ([y \<leftrightarrow> z] \<cdot> C)" using `x \<notin> PFV B` by auto
            hence "x \<notin> [y \<leftrightarrow> z] {$} PFV C" using pretrm_prm_fvs by metis
            consider "z \<in> PFV C" | "z \<notin> PFV C" by auto
            thus ?thesis proof(cases)
              case 1
                hence "[y \<leftrightarrow> z] {$} PFV C = PFV C - {z} \<union> {y}"
                  using prm_set_unit_action prm_unit_commutes
                  and `z \<in> PFV C` `y \<notin> PFV C` by metis
                hence "x \<notin> PFV C - {z} \<union> {y}" using `x \<notin> [y \<leftrightarrow> z] {$} PFV C` by auto
                hence "x \<notin> PFV C - {z}" using `x \<noteq> y` by auto
                thus ?thesis using `x \<noteq> z` by auto
              next
              case 2
                hence "[y \<leftrightarrow> z] {$} PFV C = PFV C" using prm_set_unit_inaction `y \<notin> PFV C` by metis
                thus ?thesis using `x \<notin> [y \<leftrightarrow> z] {$} PFV C` by auto
              next
            qed
          qed

          have "A =a [x \<leftrightarrow> z] \<cdot> C" proof -
            have "A =a ([x \<leftrightarrow> y] \<circ> [y \<leftrightarrow> z]) \<cdot> C"
              using IH * `A =a [x \<leftrightarrow> y] \<cdot> B` `B =a [y \<leftrightarrow> z] \<cdot> C`
              and pretrm_alpha_equiv_prm pretrm_prm_apply_compose by metis

            have "([x \<leftrightarrow> y] \<circ> [y \<leftrightarrow> z]) \<cdot> C =a [x \<leftrightarrow> z] \<cdot> C" proof -
              have "prm_disagreement ([x \<leftrightarrow> y] \<circ> [y \<leftrightarrow> z]) [x \<leftrightarrow> z] = {x, y}"
                using `x \<noteq> y` `y \<noteq> z` `x \<noteq> z` prm_disagreement_composition by metis

              hence "\<And>a. a \<in> prm_disagreement ([x \<leftrightarrow> y] \<circ> [y \<leftrightarrow> z]) [x \<leftrightarrow> z] \<Longrightarrow> a \<notin> PFV C"
                using `x \<notin> PFV C` `y \<notin> PFV C`
                using Diff_iff Diff_insert_absorb insert_iff by auto
              thus ?thesis using pretrm_prm_agreement_equiv by metis
            qed

            thus ?thesis using IH *
              using `A =a ([x \<leftrightarrow> y] \<circ> [y \<leftrightarrow> z]) \<cdot> C` `([x \<leftrightarrow> y] \<circ> [y \<leftrightarrow> z]) \<cdot> C =a [x \<leftrightarrow> z] \<cdot> C`
              by metis
          qed

          show ?thesis using `x \<noteq> z` `A =a [x \<leftrightarrow> z] \<cdot> C` `x \<notin> PFV C` X Z
            using pretrm_alpha_equiv.fn2 by metis
        next
      qed
    next
  qed
qed

corollary pretrm_alpha_equiv_transp:
  shows "transp pretrm_alpha_equiv"
unfolding transp_def using pretrm_alpha_equiv_transitive by auto

quotient_type 'a trm = "'a pretrm" / pretrm_alpha_equiv
proof(rule equivpI)
  show "reflp  pretrm_alpha_equiv" using pretrm_alpha_equiv_reflp.
  show "symp   pretrm_alpha_equiv" using pretrm_alpha_equiv_symp.
  show "transp pretrm_alpha_equiv" using pretrm_alpha_equiv_transp.
qed

lift_definition Var :: "'a \<Rightarrow> 'a trm" is PVar.
lift_definition App :: "'a trm \<Rightarrow> 'a trm \<Rightarrow> 'a trm" is PApp using pretrm_alpha_equiv.app.
lift_definition Fn  :: "'a \<Rightarrow> type \<Rightarrow> 'a trm \<Rightarrow> 'a trm" is PFn using pretrm_alpha_equiv.fn1.
lift_definition FV :: "'a trm \<Rightarrow> 'a set" is PFV using pretrm_alpha_equiv_fvs.

context fresh
begin
lemma pretrm_fresh_fn:
  shows "PFn x T X =a PFn (gen_fresh (PFV X)) T ([x \<leftrightarrow> gen_fresh (PFV X)] \<cdot> X)"
proof -
  consider "x = gen_fresh (PFV X)" | "x \<noteq> gen_fresh (PFV X)" by auto
  thus ?thesis proof(cases)
    case 1
      hence "X =a [x \<leftrightarrow> gen_fresh (PFV X)] \<cdot> X"
        using prm_unit_equal_id pretrm_prm_apply_id pretrm_alpha_equiv_reflexive by metis
      thus ?thesis using pretrm_alpha_equiv.fn1 `x = gen_fresh (PFV X)` by metis
    next
    case 2
      have "x \<notin> PFV ([x \<leftrightarrow> gen_fresh (PFV X)] \<cdot> X)"
      proof -
        have "finite (PFV X)" using pretrm_fvs_finite.
        hence "gen_fresh (PFV X) \<notin> PFV X" using fresh_axioms unfolding fresh_def by metis
        have *: "PFV ([x \<leftrightarrow> gen_fresh (PFV X)] \<cdot> X) = [x \<leftrightarrow> gen_fresh (PFV X)] {$} PFV X"
          using pretrm_prm_fvs.
        consider "x \<in> PFV X" | "x \<notin> PFV X" by auto
        thus ?thesis proof(cases)
          case 1
            hence "PFV ([x \<leftrightarrow> gen_fresh (PFV X)] \<cdot> X) = PFV X - {x} \<union> {gen_fresh (PFV X)}"
              using * prm_set_unit_action `gen_fresh (PFV X) \<notin> PFV X` by metis
            thus ?thesis using `x \<noteq> gen_fresh (PFV X)` by auto
          next
          case 2
            hence "PFV ([x \<leftrightarrow> gen_fresh (PFV X)] \<cdot> X) = PFV X"
              using * prm_set_unit_inaction `gen_fresh (PFV X) \<notin> PFV X` by metis
            thus ?thesis using `x \<notin> PFV X` by auto
          next
        qed
      qed
      moreover have "X =a [x \<leftrightarrow> gen_fresh (PFV X)] \<cdot> [x \<leftrightarrow> gen_fresh (PFV X)] \<cdot> X"
        using pretrm_prm_apply_compose prm_unit_involution pretrm_prm_apply_id
        using pretrm_alpha_equiv_reflexive by metis
      ultimately show ?thesis using pretrm_alpha_equiv.fn2 `x \<noteq> gen_fresh (PFV X)` by metis
    next
  qed
qed
end

lemma trm_induct:
  fixes P :: "'a trm \<Rightarrow> bool"
  assumes
    "\<And>x. P (Var x)"
    "\<And>A B. \<lbrakk>P A; P B\<rbrakk> \<Longrightarrow> P (App A B)"
    "\<And>x T A. P A \<Longrightarrow> P (Fn x T A)"
  shows "P M"
proof -
  have "\<And>X. P (abs_trm X)"
  proof(rule pretrm.induct)
    show "\<And>X x. P (abs_trm (PVar x))"
      using assms(1) Var.abs_eq by metis
    show "\<And>X A B. \<lbrakk>P (abs_trm A); P (abs_trm B)\<rbrakk> \<Longrightarrow> P (abs_trm (PApp A B))"
      using assms(2) App.abs_eq by metis
    show "\<And>X x T A. P (abs_trm A) \<Longrightarrow> P (abs_trm (PFn x T A))"
      using assms(3) Fn.abs_eq by metis
  qed
  thus ?thesis using trm.abs_induct by auto
qed

lemma trm_strong_induct:
  fixes P :: "'a set \<Rightarrow> 'a trm \<Rightarrow> bool"
  assumes
    "\<And>c x. P c (Var x)"
    "\<And>c A B. \<lbrakk>\<And>c'. P c' A; \<And>c'. P c' B\<rbrakk> \<Longrightarrow> P c (App A B)"
    "\<And>c x T A. \<lbrakk>x \<notin> c; \<And>c'. P c' A\<rbrakk> \<Longrightarrow> P c (Fn x T A)"
  shows "\<And>c. P c M"
proof -
  have "\<And>c X. P c (abs_trm X)"
  proof(rule pretrm.induct)
    show "\<And>c X x. P c (abs_trm (PVar x))"
      using assms(1) Var.abs_eq by metis
    show "\<And>c X A B. \<lbrakk>P c (abs_trm A); P c (abs_trm B)\<rbrakk> \<Longrightarrow> P c (abs_trm (PApp A B))"
    proof -
      fix c X A B
      assume "P c (abs_trm A)"
      hence "\<And>c'. P c' (abs_trm A)" 
qed

type_synonym 'a typing_ctx = "'a \<rightharpoonup> type"

fun pretrm_subst :: "'a pretrm \<Rightarrow> 'a \<Rightarrow> 'a pretrm \<Rightarrow> 'a pretrm" where
  "pretrm_subst (PVar x)    y M = (if x = y then M else PVar x)"
| "pretrm_subst (PApp A B)  y M = PApp (pretrm_subst A y M) (pretrm_subst B y M)"
| "pretrm_subst (PFn x T A) y M = PFn x T (if x = y then A else pretrm_subst A y M)"

lemma pretrm_subst_fresh:
  assumes "a \<notin> PFV X"
  shows "a \<notin> PFV (pretrm_subst X a Y)"
using assms by(induction X, auto)

lift_definition trm_subst :: "'a trm \<Rightarrow> 'a \<Rightarrow> 'a trm \<Rightarrow> 'a trm" ("_[_ := _]") is pretrm_subst
proof -
  fix y :: 'a
  fix A B C D :: "'a pretrm"
  assume "A =a B" "C =a D"
  thus "pretrm_subst A y C =a pretrm_subst B y D"
  proof(induction rule: pretrm_alpha_equiv.induct)
    case (var x)
      thus ?case by(cases "x = y", auto simp add: pretrm_alpha_equiv.var)
    next
    case (app E F G H)
      thus ?case by(simp add: pretrm_alpha_equiv.app)
    next
    case (fn1 A B x T)
      thus ?case by(simp add: pretrm_alpha_equiv.fn1)
    next
    case (fn2 a b A B T)
      consider "y = a" | "y = b" | "y \<noteq> a \<and> y \<noteq> b" by auto
      thus ?case proof(cases)
        case 1
          hence *:
            "pretrm_subst (PFn a T A) y C = PFn a T A"
            "pretrm_subst (PFn b T B) y D = PFn b T (pretrm_subst B a D)"
          using `a \<noteq> b` by auto
          have "a \<notin> PFV (pretrm_subst B a D)" using `a \<notin> PFV B` pretrm_subst_fresh by metis
          moreover have "A =a [a \<leftrightarrow> b] \<cdot> (pretrm_subst B a D)" sorry
          ultimately show ?thesis using `a \<noteq> b` * pretrm_alpha_equiv.fn2 by metis
        next
          
inductive typing :: "'a typing_ctx \<Rightarrow> 'a trm \<Rightarrow> type \<Rightarrow> bool" ("_ \<turnstile> _ : _") where
  tvar: "\<Gamma> x = Some \<tau> \<Longrightarrow> \<Gamma> \<turnstile> Var x : \<tau>"
| tapp: "\<lbrakk>\<Gamma> \<turnstile> f : TArr \<tau> \<sigma>; \<Gamma> \<turnstile> x : \<tau>\<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> App f x : \<sigma>"
| tfn:  "\<Gamma>(x \<mapsto> \<tau>) \<turnstile> A : \<sigma> \<Longrightarrow> \<Gamma> \<turnstile> Fn x \<tau> A : TArr \<tau> \<sigma>"
end
