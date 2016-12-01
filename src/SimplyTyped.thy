theory SimplyTyped
imports Main Permutation
begin

type_synonym tvar = nat

datatype type =
  TVar tvar
| TArr type type

datatype 'a pretrm =
  Var 'a
| App "'a pretrm" "'a pretrm"
| Fn 'a type "'a pretrm"

fun FV :: "'a pretrm \<Rightarrow> 'a set" where
  "FV (Var x) = {x}"
| "FV (App A B) = FV A \<union> FV B"
| "FV (Fn x _ A) = FV A - {x}"

fun pretrm_apply_prm :: "'a prm \<Rightarrow> 'a pretrm \<Rightarrow> 'a pretrm" (infixr "\<cdot>" 150) where
  "pretrm_apply_prm \<pi> (Var x) = Var (\<pi> $ x)"
| "pretrm_apply_prm \<pi> (App A B) = App (pretrm_apply_prm \<pi> A) (pretrm_apply_prm \<pi> B)"
| "pretrm_apply_prm \<pi> (Fn x T A) = Fn (\<pi> $ x) T (pretrm_apply_prm \<pi> A)"

inductive pretrm_alpha_equiv :: "'a pretrm \<Rightarrow> 'a pretrm \<Rightarrow> bool" (infix "=a" 100) where
  var:        "(Var x) =a (Var x)"
| app:        "\<lbrakk>A =a B; C =a D\<rbrakk> \<Longrightarrow> (App A C) =a (App B D)"
| fn1:        "A =a B \<Longrightarrow> (Fn x T A) =a (Fn x T B)"
| fn2:        "\<lbrakk>a \<noteq> b; A =a [a \<leftrightarrow> b] \<cdot> B; a \<notin> FV B\<rbrakk> \<Longrightarrow> (Fn a T A) =a (Fn b T B)"

inductive_cases varE: "Var x =a Y"
inductive_cases appE: "App A B =a Y"
inductive_cases fnE:  "Fn x T A =a Y"

fun pretrm_size :: "'a pretrm \<Rightarrow> nat" where
  "pretrm_size (Var _) = 1"
| "pretrm_size (App A B) = pretrm_size A + pretrm_size B + 1"
| "pretrm_size (Fn x T A) = pretrm_size A + 1"

section{*lemmas*}
lemma pretrm_size_nonzero:
  shows "pretrm_size M \<noteq> 0"
by(cases M, simp_all)

lemma pretrm_size_app1:
  shows "pretrm_size A < pretrm_size (App A B)"
by(induction A, simp_all)

lemma pretrm_size_app2:
  shows "pretrm_size B < pretrm_size (App A B)"
by(induction B, simp_all)

lemma pretrm_size_fn:
  shows "pretrm_size A < pretrm_size (Fn x T A)"
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

lemma pretrm_prm_fvs:
  shows "FV (\<pi> \<cdot> X) = \<pi> {$} FV X"
proof(induction X)
  case (Var x)
    have "FV (\<pi> \<cdot> Var x) = FV (Var (\<pi> $ x))" by simp
    moreover have "... = {\<pi> $ x}" by simp
    moreover have "... = \<pi> {$} {x}" using prm_set_singleton by metis
    moreover have "... = \<pi> {$} FV (Var x)" by simp
    ultimately show ?case by metis
  next
  case (App A B)
    have "FV (\<pi> \<cdot> App A B) = FV (App (\<pi> \<cdot> A) (\<pi> \<cdot> B))" by simp
    moreover have "... = FV (\<pi> \<cdot> A) \<union> FV (\<pi> \<cdot> B)" by simp
    moreover have "... = \<pi> {$} FV A \<union> \<pi> {$} FV B" using App.IH by metis
    moreover have "... = \<pi> {$} (FV A \<union> FV B)" using prm_set_distributes_union by metis
    moreover have "... = \<pi> {$} FV (App A B)" by simp
    ultimately show ?case by metis
  next
  case (Fn x T A)
    have "FV (\<pi> \<cdot> Fn x T A) = FV (Fn (\<pi> $ x) T (\<pi> \<cdot> A))" by simp
    moreover have "... = FV (\<pi> \<cdot> A) - {\<pi> $ x}" by simp
    moreover have "... = \<pi> {$} FV A - {\<pi> $ x}" using Fn.IH by metis
    moreover have "... = \<pi> {$} FV A - \<pi> {$} {x}" using prm_set_singleton by metis
    moreover have "... = \<pi> {$} (FV A - {x})" using prm_set_distributes_difference by metis
    moreover have "... = \<pi> {$} FV (Fn x T A)" by simp
    ultimately show ?case by metis
  next
qed

lemma pretrm_alpha_equiv_fvs:
  assumes "X =a Y"
  shows "FV X = FV Y"
using assms proof(induction rule: pretrm_alpha_equiv.induct, simp, simp, simp)
  case (fn2 a b A B T)
    have "FV (Fn a T A) = FV A - {a}" by simp
    moreover have "... = FV ([a \<leftrightarrow> b] \<cdot> B) - {a}" using fn2.IH by metis
    moreover have "... = ([a \<leftrightarrow> b] {$} FV B) - {a}" using pretrm_prm_fvs by metis
    moreover have "... = FV B - {b}"  proof -
      consider "b \<in> FV B" | "b \<notin> FV B" by auto
      thus ?thesis proof(cases)
        case 1
          thm prm_set_unit_action[where ?S = "FV B" and ?a = b and ?b = a]
          have "[a \<leftrightarrow> b] {$} FV B - {a} = [b \<leftrightarrow> a] {$} FV B - {a}" using prm_unit_commutes by metis
          moreover have "... = ((FV B - {b}) \<union> {a}) - {a}"
            using prm_set_unit_action `b \<in> FV B` `a \<notin> FV B` by metis
          moreover have "... = FV B - {b}" using `a \<notin> FV B` `a \<noteq> b`
            using Diff_insert0 Diff_insert2 Un_insert_right insert_Diff1 insert_is_Un singletonI
              sup_bot.right_neutral by blast (* why?! *)
          ultimately show ?thesis by metis
        next
        case 2
          hence "[a \<leftrightarrow> b] {$} FV B - {a} = FV B - {a}"
            using prm_set_unit_inaction `a \<notin> FV B` by metis
          moreover have "... = FV B" using `a \<notin> FV B` by simp
          moreover have "... = FV B - {b}" using `b \<notin> FV B` by simp
          ultimately show ?thesis by metis
        next
      qed
    qed
    moreover have "... = FV (Fn b T B)" by simp
    ultimately show ?case by metis
  next
qed

lemma pretrm_alpha_equiv_prm:
  assumes "X =a Y"
  shows "[c \<leftrightarrow> d] \<cdot> X =a [c \<leftrightarrow> d] \<cdot> Y"
using assms proof(induction)
  case (var x)
    have "[c \<leftrightarrow> d] \<cdot> Var x = Var ([c \<leftrightarrow> d] $ x)" by simp
    thus ?case using pretrm_alpha_equiv.var by metis
  next
  case (app A B C D)
    have "[c \<leftrightarrow> d] \<cdot> App A C = App ([c \<leftrightarrow> d] \<cdot> A) ([c \<leftrightarrow> d] \<cdot> C)"
    and  "[c \<leftrightarrow> d] \<cdot> App B D = App ([c \<leftrightarrow> d] \<cdot> B) ([c \<leftrightarrow> d] \<cdot> D)" by simp_all
    thus ?case using app.IH pretrm_alpha_equiv.app by metis
  next
  case (fn1 A B x T)
    have "[c \<leftrightarrow> d] \<cdot> (Fn x T A) = Fn ([c \<leftrightarrow> d] $ x) T ([c \<leftrightarrow> d] \<cdot> A)"
    and  "[c \<leftrightarrow> d] \<cdot> (Fn x T B) = Fn ([c \<leftrightarrow> d] $ x) T ([c \<leftrightarrow> d] \<cdot> B)"
      by simp_all
    thus ?case using fn1.IH pretrm_alpha_equiv.fn1 by metis
  next
  case (fn2 a b A B T)
    have A_simp: "[c \<leftrightarrow> d] \<cdot> Fn a T A = Fn ([c \<leftrightarrow> d] $ a) T ([c \<leftrightarrow> d] \<cdot> A)"
    and  B_simp: "[c \<leftrightarrow> d] \<cdot> Fn b T B = Fn ([c \<leftrightarrow> d] $ b) T ([c \<leftrightarrow> d] \<cdot> B)" by simp_all
    
    have "[c \<leftrightarrow> d] $ a \<noteq> [c \<leftrightarrow> d] $ b" using prm_apply_unequal `a \<noteq> b` by metis
    moreover have "[c \<leftrightarrow> d] \<cdot> A =a [[c \<leftrightarrow> d] $ a \<leftrightarrow> [c \<leftrightarrow> d] $ b] \<cdot> [c \<leftrightarrow> d] \<cdot> B" sorry
    moreover have "[c \<leftrightarrow> d] $ a \<notin> FV ([c \<leftrightarrow> d] \<cdot> B)" proof -
      consider "a = c" | "a = d" | "a \<noteq> c \<and> a \<noteq> d" by auto
      hence "[c \<leftrightarrow> d] $ a \<notin> [c \<leftrightarrow> d] {$} FV B" sorry
      thus ?thesis using pretrm_prm_fvs by metis
    qed
    ultimately have "Fn ([c \<leftrightarrow> d] $ a) T ([c \<leftrightarrow> d] \<cdot> A) =a Fn ([c \<leftrightarrow> d] $ b) T ([c \<leftrightarrow> d] \<cdot> B)"
      using pretrm_alpha_equiv.fn2 by metis
    thus ?case using A_simp B_simp by auto
  next
qed

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
  assumes "A =a [a \<leftrightarrow> b] \<cdot> B" and "a \<notin> FV B" and "a \<noteq> b"
  shows "b \<notin> FV A"
proof(cases "b \<in> FV B")
  case True
    have *: "b \<notin> FV B - {b} \<union> {a}" using assms by simp
    have "FV A = FV ([a \<leftrightarrow> b] \<cdot> B)" using pretrm_alpha_equiv_fvs assms by metis
    moreover have "... = [a \<leftrightarrow> b] {$} FV B" using pretrm_prm_fvs by metis
    moreover have "... = [b \<leftrightarrow> a] {$} FV B" using prm_unit_commutes by metis
    moreover have "... = FV B - {b} \<union> {a}" using prm_set_unit_action `a \<notin> FV B` `b \<in> FV B` by metis
    ultimately have "FV A = FV B - {b} \<union> {a}" by metis
    thus ?thesis using * by auto
  next
  case False
    have "FV A = FV ([a \<leftrightarrow> b] \<cdot> B)" using pretrm_alpha_equiv_fvs assms by metis
    moreover have "FV ([a \<leftrightarrow> b] \<cdot> B) = [a \<leftrightarrow> b] {$} FV B" using pretrm_prm_fvs by metis
    moreover have "... = FV B" using prm_set_unit_inaction `a \<notin> FV B` `b \<notin> FV B` by metis
    ultimately have "FV A = FV B" by metis
    thus ?thesis using `b \<notin> FV B` by auto
  next
qed

lemma pretrm_prm_agreement_equiv:
  assumes "\<And>a. a \<in> prm_disagreement \<pi> \<sigma> \<Longrightarrow> a \<notin> FV M"
  shows "\<pi> \<cdot> M =a \<sigma> \<cdot> M"
using assms proof(induction M)
  case (Var x)
    have "\<pi> \<cdot> (Var x) = Var (\<pi> $ x)" and "\<sigma> \<cdot> (Var x) = Var (\<sigma> $ x)" by auto

    have "x \<in> FV (Var x)" by simp
    hence "x \<notin> prm_disagreement \<pi> \<sigma>" using Var.prems by auto
    hence "\<pi> $ x = \<sigma> $ x" using prm_agreement by metis
    hence "Var (\<pi> $ x) =a Var (\<sigma> $ x)" using pretrm_alpha_equiv.var by metis
    thus ?case using `\<pi> \<cdot> (Var x) = Var (\<pi> $ x)` `\<sigma> \<cdot> (Var x) = Var (\<sigma> $ x)` by metis
  next
  case (App A B)
    hence "\<pi> \<cdot> A =a \<sigma> \<cdot> A" and "\<pi> \<cdot> B =a \<sigma> \<cdot> B" by auto
    thus ?case using pretrm_alpha_equiv.app by auto
  next
  case (Fn x T A)
    thus ?case sorry
  next
qed

section{*equivalence relation*}

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

    have "b \<notin> FV A" using `a \<notin> FV B` `A =a [a \<leftrightarrow> b] \<cdot> B` `a \<noteq> b`
      using pretrm_alpha_equiv_fvs_transfer by metis

    show ?case using `b \<noteq> a` `B =a [b \<leftrightarrow> a] \<cdot> A` `b \<notin> FV A`
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
    case (Var x)
      hence "Var x =a Y" using `X =a Y` by auto
      hence "Y = Var x" using varE by metis
      hence "Var x =a Z" using `Y =a Z` by auto
      hence "Z = Var x" using varE by metis
      thus ?thesis using pretrm_alpha_equiv.var `X = Var x` by metis
    next
    case (App A B)
      obtain C D where "Y = App C D" and "A =a C" and "B =a D"
        using appE `X = App A B` `X =a Y` by metis
      hence "App C D =a Z" using `Y =a Z` by simp
      from this obtain E F where "Z = App E F" and "C =a E" and "D =a F" using appE by metis

      have "pretrm_size A < pretrm_size X" and "pretrm_size B < pretrm_size X"
        using pretrm_size_app1 pretrm_size_app2 `X = App A B` by auto
      hence "A =a E" and "B =a F" using IH `A =a C` `C =a E` `B =a D` `D =a F` by auto
      thus ?thesis using `X = App A B` `Z = App E F` pretrm_alpha_equiv.app by metis
    next
    case (Fn x T A)
      from this have X: "X = Fn x T A".
      hence *: "pretrm_size A < pretrm_size X" using pretrm_size_fn by auto

      obtain y B where "Y = Fn y T B"
        and Y_cases: "(x = y \<and> A =a B) \<or> (x \<noteq> y \<and> A =a [x \<leftrightarrow> y] \<cdot> B \<and> x \<notin> FV B)"
        using fnE `X =a Y` `X = Fn x T A` by metis
      obtain z C where Z: "Z = Fn z T C"
        and Z_cases: "(y = z \<and> B =a C) \<or> (y \<noteq> z \<and> B =a [y \<leftrightarrow> z] \<cdot> C \<and> y \<notin> FV C)"
        using fnE `Y =a Z` `Y = Fn y T B` by metis

      consider
        "x = y" "A =a B" and "y = z" "B =a C"
      | "x = y" "A =a B" and "y \<noteq> z" "B =a [y \<leftrightarrow> z] \<cdot> C" "y \<notin> FV C"
      | "x \<noteq> y" "A =a [x \<leftrightarrow> y] \<cdot> B" "x \<notin> FV B" and "y = z" "B =a C"
      | "x \<noteq> y" "A =a [x \<leftrightarrow> y] \<cdot> B" "x \<notin> FV B" and "y \<noteq> z" "B =a [y \<leftrightarrow> z] \<cdot> C" "y \<notin> FV C" and "x = z"
      | "x \<noteq> y" "A =a [x \<leftrightarrow> y] \<cdot> B" "x \<notin> FV B" and "y \<noteq> z" "B =a [y \<leftrightarrow> z] \<cdot> C" "y \<notin> FV C" and "x \<noteq> z"
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
          have "x \<notin> FV C" using `x = y` `y \<notin> FV C` by metis
          thus ?thesis using `x \<noteq> z` `A =a [x \<leftrightarrow> z] \<cdot> C` `x \<notin> FV C` X Z
            using pretrm_alpha_equiv.fn2 by metis
        next
        case 3
          have "x \<noteq> z" using `x \<noteq> y` `y = z` by metis
          have "[x \<leftrightarrow> y] \<cdot> B =a [x \<leftrightarrow> y] \<cdot> C" using `B =a C` pretrm_alpha_equiv_prm by metis
          have "A =a [x \<leftrightarrow> z] \<cdot> C"
            using `A =a [x \<leftrightarrow> y] \<cdot> B` `[x \<leftrightarrow> y] \<cdot> B =a [x \<leftrightarrow> y] \<cdot> C` `y = z` IH *
            by metis
          have "x \<notin> FV C" using `B =a C` `x \<notin> FV B` pretrm_alpha_equiv_fvs by metis
          thus ?thesis using `x \<noteq> z` `A =a [x \<leftrightarrow> z] \<cdot> C` `x \<notin> FV C` X Z
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
          have "x \<notin> FV C" proof -
            have "FV B = FV ([y \<leftrightarrow> z] \<cdot> C)"
              using pretrm_alpha_equiv_fvs `B =a [y \<leftrightarrow> z] \<cdot> C` by metis
            hence "x \<notin> FV ([y \<leftrightarrow> z] \<cdot> C)" using `x \<notin> FV B` by auto
            hence "x \<notin> [y \<leftrightarrow> z] {$} FV C" using pretrm_prm_fvs by metis
            consider "z \<in> FV C" | "z \<notin> FV C" by auto
            thus ?thesis proof(cases)
              case 1
                hence "[y \<leftrightarrow> z] {$} FV C = FV C - {z} \<union> {y}"
                  using prm_set_unit_action prm_unit_commutes
                  and `z \<in> FV C` `y \<notin> FV C` by metis
                hence "x \<notin> FV C - {z} \<union> {y}" using `x \<notin> [y \<leftrightarrow> z] {$} FV C` by auto
                hence "x \<notin> FV C - {z}" using `x \<noteq> y` by auto
                thus ?thesis using `x \<noteq> z` by auto
              next
              case 2
                hence "[y \<leftrightarrow> z] {$} FV C = FV C" using prm_set_unit_inaction `y \<notin> FV C` by metis
                thus ?thesis using `x \<notin> [y \<leftrightarrow> z] {$} FV C` by auto
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

              hence "\<And>a. a \<in> prm_disagreement ([x \<leftrightarrow> y] \<circ> [y \<leftrightarrow> z]) [x \<leftrightarrow> z] \<Longrightarrow> a \<notin> FV C"
                using `x \<notin> FV C` `y \<notin> FV C`
                using Diff_iff Diff_insert_absorb insert_iff by auto
              thus ?thesis using pretrm_prm_agreement_equiv by metis
            qed

            thus ?thesis using IH *
              using `A =a ([x \<leftrightarrow> y] \<circ> [y \<leftrightarrow> z]) \<cdot> C` `([x \<leftrightarrow> y] \<circ> [y \<leftrightarrow> z]) \<cdot> C =a [x \<leftrightarrow> z] \<cdot> C`
              by metis
          qed

          show ?thesis using `x \<noteq> z` `A =a [x \<leftrightarrow> z] \<cdot> C` `x \<notin> FV C` X Z
            using pretrm_alpha_equiv.fn2 by metis
        next
      qed
    next
  qed
qed

corollary pretrm_alpha_equiv_transp:
  shows "transp pretrm_alpha_equiv"
unfolding transp_def using pretrm_alpha_equiv_transitive by auto

section{*typing judgement*}
type_synonym 'a typing_ctx = "'a \<rightharpoonup> type"

(* define permutations on typing contexts? *)
(* somehow define the typing rules on the quotient type? *)

inductive typing :: "'a typing_ctx \<Rightarrow> 'a pretrm \<Rightarrow> type \<Rightarrow> bool" ("_ \<turnstile> _ : _") where
  tvar: "\<Gamma> x = Some \<tau> \<Longrightarrow> \<Gamma> \<turnstile> Var x : \<tau>"
| tapp: "\<lbrakk>\<Gamma> \<turnstile> f : TArr \<tau> \<sigma>; \<Gamma> \<turnstile> x : \<tau>\<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> App f x : \<sigma>"
| tfn:  "\<Gamma>(x \<mapsto> \<tau>) \<turnstile> M : \<sigma> \<Longrightarrow> \<Gamma> \<turnstile> Fn x \<tau> M : TArr \<tau> \<sigma>"

inductive_cases tvarE: "\<Gamma> \<turnstile> Var x : \<tau>"
inductive_cases tappE: "\<Gamma> \<turnstile> App f x : \<sigma>"
inductive_cases tfnE:  "\<Gamma> \<turnstile> Fn x \<tau> M : \<sigma>"

lemma typing_prm_invariant:
  assumes "\<Gamma> \<turnstile> X : \<tau>"
  shows "\<Gamma>' \<turnstile> \<pi> \<cdot> X : \<tau>"


lemma typing_alpha_equiv_invariant:
  assumes "X =a Y" and "\<Gamma> \<turnstile> X : \<tau>" "\<Gamma> \<turnstile> Y : \<sigma>"
  shows "\<tau> = \<sigma>"
using assms proof(induction arbitrary: \<Gamma> \<tau> \<sigma> rule: pretrm_alpha_equiv.induct)
  case (var x)
    hence "\<Gamma> x = Some \<tau>" and "\<Gamma> x = Some \<sigma>" using tvarE by metis+
    thus ?case by auto
  next
  case (app A B C D)
    obtain \<alpha> where A: "\<Gamma> \<turnstile> A : TArr \<alpha> \<tau>" and "\<Gamma> \<turnstile> C : \<alpha>" using app.prems app.IH tappE by metis
    obtain \<beta> where B: "\<Gamma> \<turnstile> B : TArr \<beta> \<sigma>" and "\<Gamma> \<turnstile> D : \<beta>" using app.prems app.IH tappE by metis
    thus ?case using A B using app.IH type.inject by metis
  next
  case (fn1 A B x T)
    obtain \<alpha> \<beta>
      where A: "\<Gamma>(x \<mapsto> T) \<turnstile> A : \<alpha>" "\<tau> = TArr T \<alpha>"
      and   B: "\<Gamma>(x \<mapsto> T) \<turnstile> B : \<beta>" "\<sigma> = TArr T \<beta>"
      using fn1.prems tfnE by metis
    thus ?case using fn1.prems fn1.IH by metis
  next
  case (fn2 a b A B T)
    thus ?case sorry
  next
qed

section{*quotient type*}
quotient_type 'a trm = "'a pretrm" / pretrm_alpha_equiv
proof(rule equivpI)
  show "reflp  pretrm_alpha_equiv" using pretrm_alpha_equiv_reflp.
  show "symp   pretrm_alpha_equiv" using pretrm_alpha_equiv_symp.
  show "transp pretrm_alpha_equiv" using pretrm_alpha_equiv_transp.
qed

end
