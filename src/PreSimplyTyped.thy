theory PreSimplyTyped
imports Main Permutation
begin

type_synonym tvar = nat

datatype type =
  TVar tvar
| TArr type type

datatype 'a ptrm =
  PVar 'a
| PApp "'a ptrm" "'a ptrm"
| PFn 'a type "'a ptrm"

fun ptrm_fvs :: "'a ptrm \<Rightarrow> 'a set" where
  "ptrm_fvs (PVar x) = {x}"
| "ptrm_fvs (PApp A B) = ptrm_fvs A \<union> ptrm_fvs B"
| "ptrm_fvs (PFn x _ A) = ptrm_fvs A - {x}"

fun ptrm_apply_prm :: "'a prm \<Rightarrow> 'a ptrm \<Rightarrow> 'a ptrm" (infixr "\<cdot>" 150) where
  "ptrm_apply_prm \<pi> (PVar x) = PVar (\<pi> $ x)"
| "ptrm_apply_prm \<pi> (PApp A B) = PApp (ptrm_apply_prm \<pi> A) (ptrm_apply_prm \<pi> B)"
| "ptrm_apply_prm \<pi> (PFn x T A) = PFn (\<pi> $ x) T (ptrm_apply_prm \<pi> A)"

inductive ptrm_alpha_equiv :: "'a ptrm \<Rightarrow> 'a ptrm \<Rightarrow> bool" (infix "=a" 100) where
  var:        "(PVar x) =a (PVar x)"
| app:        "\<lbrakk>A =a B; C =a D\<rbrakk> \<Longrightarrow> (PApp A C) =a (PApp B D)"
| fn1:        "A =a B \<Longrightarrow> (PFn x T A) =a (PFn x T B)"
| fn2:        "\<lbrakk>a \<noteq> b; A =a [a \<leftrightarrow> b] \<cdot> B; a \<notin> ptrm_fvs B\<rbrakk> \<Longrightarrow> (PFn a T A) =a (PFn b T B)"

inductive_cases varE: "PVar x =a Y"
inductive_cases appE: "PApp A B =a Y"
inductive_cases fnE:  "PFn x T A =a Y"

fun ptrm_size :: "'a ptrm \<Rightarrow> nat" where
  "ptrm_size (PVar _) = 1"
| "ptrm_size (PApp A B) = ptrm_size A + ptrm_size B + 1"
| "ptrm_size (PFn x T A) = ptrm_size A + 1"

lemma ptrm_size_app1:
  shows "ptrm_size A < ptrm_size (PApp A B)"
by(induction A, simp_all)

lemma ptrm_size_app2:
  shows "ptrm_size B < ptrm_size (PApp A B)"
by(induction B, simp_all)

lemma ptrm_size_fn:
  shows "ptrm_size A < ptrm_size (PFn x T A)"
by(induction A, simp_all)

lemma ptrm_prm_apply_id:
  shows "\<epsilon> \<cdot> X = X"
by(induction X, simp_all add: prm_apply_id)

lemma ptrm_prm_apply_compose:
  shows "\<pi> \<cdot> \<sigma> \<cdot> X = (\<pi> \<diamondop> \<sigma>) \<cdot> X"
by(induction X, simp_all add: prm_apply_composition)

lemma ptrm_fvs_finite:
  shows "finite (ptrm_fvs X)"
by(induction X, auto)

lemma ptrm_prm_fvs:
  shows "ptrm_fvs (\<pi> \<cdot> X) = \<pi> {$} ptrm_fvs X"
proof(induction X)
  case (PVar x)
    have "ptrm_fvs (\<pi> \<cdot> PVar x) = ptrm_fvs (PVar (\<pi> $ x))" by simp
    moreover have "... = {\<pi> $ x}" by simp
    moreover have "... = \<pi> {$} {x}" using prm_set_singleton by metis
    moreover have "... = \<pi> {$} ptrm_fvs (PVar x)" by simp
    ultimately show ?case by metis
  next
  case (PApp A B)
    have "ptrm_fvs (\<pi> \<cdot> PApp A B) = ptrm_fvs (PApp (\<pi> \<cdot> A) (\<pi> \<cdot> B))" by simp
    moreover have "... = ptrm_fvs (\<pi> \<cdot> A) \<union> ptrm_fvs (\<pi> \<cdot> B)" by simp
    moreover have "... = \<pi> {$} ptrm_fvs A \<union> \<pi> {$} ptrm_fvs B" using PApp.IH by metis
    moreover have "... = \<pi> {$} (ptrm_fvs A \<union> ptrm_fvs B)" using prm_set_distributes_union by metis
    moreover have "... = \<pi> {$} ptrm_fvs (PApp A B)" by simp
    ultimately show ?case by metis
  next
  case (PFn x T A)
    have "ptrm_fvs (\<pi> \<cdot> PFn x T A) = ptrm_fvs (PFn (\<pi> $ x) T (\<pi> \<cdot> A))" by simp
    moreover have "... = ptrm_fvs (\<pi> \<cdot> A) - {\<pi> $ x}" by simp
    moreover have "... = \<pi> {$} ptrm_fvs A - {\<pi> $ x}" using PFn.IH by metis
    moreover have "... = \<pi> {$} ptrm_fvs A - \<pi> {$} {x}" using prm_set_singleton by metis
    moreover have "... = \<pi> {$} (ptrm_fvs A - {x})" using prm_set_distributes_difference by metis
    moreover have "... = \<pi> {$} ptrm_fvs (PFn x T A)" by simp
    ultimately show ?case by metis
  next
qed

lemma ptrm_alpha_equiv_fvs:
  assumes "X =a Y"
  shows "ptrm_fvs X = ptrm_fvs Y"
using assms proof(induction rule: ptrm_alpha_equiv.induct, simp, simp, simp)
  case (fn2 a b A B T)
    have "ptrm_fvs (PFn a T A) = ptrm_fvs A - {a}" by simp
    moreover have "... = ptrm_fvs ([a \<leftrightarrow> b] \<cdot> B) - {a}" using fn2.IH by metis
    moreover have "... = ([a \<leftrightarrow> b] {$} ptrm_fvs B) - {a}" using ptrm_prm_fvs by metis
    moreover have "... = ptrm_fvs B - {b}"  proof -
      consider "b \<in> ptrm_fvs B" | "b \<notin> ptrm_fvs B" by auto
      thus ?thesis proof(cases)
        case 1
          thm prm_set_unit_action[where ?S = "ptrm_fvs B" and ?a = b and ?b = a]
          have "[a \<leftrightarrow> b] {$} ptrm_fvs B - {a} = [b \<leftrightarrow> a] {$} ptrm_fvs B - {a}" using prm_unit_commutes by metis
          moreover have "... = ((ptrm_fvs B - {b}) \<union> {a}) - {a}"
            using prm_set_unit_action `b \<in> ptrm_fvs B` `a \<notin> ptrm_fvs B` by metis
          moreover have "... = ptrm_fvs B - {b}" using `a \<notin> ptrm_fvs B` `a \<noteq> b`
            using Diff_insert0 Diff_insert2 Un_insert_right insert_Diff1 insert_is_Un singletonI
              sup_bot.right_neutral by blast (* why?! *)
          ultimately show ?thesis by metis
        next
        case 2
          hence "[a \<leftrightarrow> b] {$} ptrm_fvs B - {a} = ptrm_fvs B - {a}"
            using prm_set_unit_inaction `a \<notin> ptrm_fvs B` by metis
          moreover have "... = ptrm_fvs B" using `a \<notin> ptrm_fvs B` by simp
          moreover have "... = ptrm_fvs B - {b}" using `b \<notin> ptrm_fvs B` by simp
          ultimately show ?thesis by metis
        next
      qed
    qed
    moreover have "... = ptrm_fvs (PFn b T B)" by simp
    ultimately show ?case by metis
  next
qed

lemma ptrm_alpha_equiv_prm:
  assumes "X =a Y"
  shows "\<pi> \<cdot> X =a \<pi> \<cdot> Y"
sorry 

lemma ptrm_swp_transfer:
  assumes "[a \<leftrightarrow> b] \<cdot> X =a Y"
  shows "X =a [a \<leftrightarrow> b] \<cdot> Y"
proof -
  have "[a \<leftrightarrow> b] \<cdot> [a \<leftrightarrow> b] \<cdot> X =a [a \<leftrightarrow> b] \<cdot> Y"
    using assms ptrm_alpha_equiv_prm by metis
  hence "([a \<leftrightarrow> b] \<diamondop> [a \<leftrightarrow> b]) \<cdot> X =a [a \<leftrightarrow> b] \<cdot> Y" using ptrm_prm_apply_compose
    by metis
  hence "\<epsilon> \<cdot> X =a [a \<leftrightarrow> b] \<cdot> Y" using prm_unit_involution by metis
  thus ?thesis using ptrm_prm_apply_id by metis
qed

lemma ptrm_alpha_equiv_fvs_transfer:
  assumes "A =a [a \<leftrightarrow> b] \<cdot> B" and "a \<notin> ptrm_fvs B" and "a \<noteq> b"
  shows "b \<notin> ptrm_fvs A"
proof(cases "b \<in> ptrm_fvs B")
  case True
    have *: "b \<notin> ptrm_fvs B - {b} \<union> {a}" using assms by simp
    have "ptrm_fvs A = ptrm_fvs ([a \<leftrightarrow> b] \<cdot> B)" using ptrm_alpha_equiv_fvs assms by metis
    moreover have "... = [a \<leftrightarrow> b] {$} ptrm_fvs B" using ptrm_prm_fvs by metis
    moreover have "... = [b \<leftrightarrow> a] {$} ptrm_fvs B" using prm_unit_commutes by metis
    moreover have "... = ptrm_fvs B - {b} \<union> {a}" using prm_set_unit_action `a \<notin> ptrm_fvs B` `b \<in> ptrm_fvs B` by metis
    ultimately have "ptrm_fvs A = ptrm_fvs B - {b} \<union> {a}" by metis
    thus ?thesis using * by auto
  next
  case False
    have "ptrm_fvs A = ptrm_fvs ([a \<leftrightarrow> b] \<cdot> B)" using ptrm_alpha_equiv_fvs assms by metis
    moreover have "ptrm_fvs ([a \<leftrightarrow> b] \<cdot> B) = [a \<leftrightarrow> b] {$} ptrm_fvs B" using ptrm_prm_fvs by metis
    moreover have "... = ptrm_fvs B" using prm_set_unit_inaction `a \<notin> ptrm_fvs B` `b \<notin> ptrm_fvs B` by metis
    ultimately have "ptrm_fvs A = ptrm_fvs B" by metis
    thus ?thesis using `b \<notin> ptrm_fvs B` by auto
  next
qed

lemma ptrm_prm_agreement_equiv:
  assumes "\<And>a. a \<in> prm_disagreement \<pi> \<sigma> \<Longrightarrow> a \<notin> ptrm_fvs M"
  shows "\<pi> \<cdot> M =a \<sigma> \<cdot> M"
sorry

lemma ptrm_alpha_equiv_reflexive:
  shows "M =a M"
by(induction M, auto simp add: ptrm_alpha_equiv.intros)

corollary ptrm_alpha_equiv_reflp:
  shows "reflp ptrm_alpha_equiv"
unfolding reflp_def using ptrm_alpha_equiv_reflexive by auto

lemma ptrm_alpha_equiv_symmetric:
  assumes "X =a Y"
  shows "Y =a X"
using assms proof(induction rule: ptrm_alpha_equiv.induct, auto simp add: ptrm_alpha_equiv.intros)
  case (fn2 a b A B T)
    have "b \<noteq> a" using `a \<noteq> b` by auto
    have "B =a [b \<leftrightarrow> a] \<cdot> A" using `[a \<leftrightarrow> b] \<cdot> B =a A`
      using ptrm_swp_transfer prm_unit_commutes by metis

    have "b \<notin> ptrm_fvs A" using `a \<notin> ptrm_fvs B` `A =a [a \<leftrightarrow> b] \<cdot> B` `a \<noteq> b`
      using ptrm_alpha_equiv_fvs_transfer by metis

    show ?case using `b \<noteq> a` `B =a [b \<leftrightarrow> a] \<cdot> A` `b \<notin> ptrm_fvs A`
      using ptrm_alpha_equiv.fn2 by metis
  next
qed

corollary ptrm_alpha_equiv_symp:
  shows "symp ptrm_alpha_equiv"
unfolding symp_def using ptrm_alpha_equiv_symmetric by auto

lemma ptrm_alpha_equiv_transitive:
  assumes "X =a Y" and "Y =a Z"
  shows "X =a Z"
using assms proof(induction "ptrm_size X" arbitrary: X Y Z rule: less_induct)
  fix X Y Z :: "'a ptrm"
  assume IH: "\<And>K Y Z :: 'a ptrm. ptrm_size K < ptrm_size X \<Longrightarrow> K =a Y \<Longrightarrow> Y =a Z \<Longrightarrow> K =a Z"
  assume "X =a Y" and "Y =a Z"
  show "X =a Z" proof(cases X)
    case (PVar x)
      hence "PVar x =a Y" using `X =a Y` by auto
      hence "Y = PVar x" using varE by metis
      hence "PVar x =a Z" using `Y =a Z` by auto
      hence "Z = PVar x" using varE by metis
      thus ?thesis using ptrm_alpha_equiv.var `X = PVar x` by metis
    next
    case (PApp A B)
      obtain C D where "Y = PApp C D" and "A =a C" and "B =a D"
        using appE `X = PApp A B` `X =a Y` by metis
      hence "PApp C D =a Z" using `Y =a Z` by simp
      from this obtain E F where "Z = PApp E F" and "C =a E" and "D =a F" using appE by metis

      have "ptrm_size A < ptrm_size X" and "ptrm_size B < ptrm_size X"
        using ptrm_size_app1 ptrm_size_app2 `X = PApp A B` by auto
      hence "A =a E" and "B =a F" using IH `A =a C` `C =a E` `B =a D` `D =a F` by auto
      thus ?thesis using `X = PApp A B` `Z = PApp E F` ptrm_alpha_equiv.app by metis
    next
    case (PFn x T A)
      from this have X: "X = PFn x T A".
      hence *: "ptrm_size A < ptrm_size X" using ptrm_size_fn by auto

      obtain y B where "Y = PFn y T B"
        and Y_cases: "(x = y \<and> A =a B) \<or> (x \<noteq> y \<and> A =a [x \<leftrightarrow> y] \<cdot> B \<and> x \<notin> ptrm_fvs B)"
        using fnE `X =a Y` `X = PFn x T A` by metis
      obtain z C where Z: "Z = PFn z T C"
        and Z_cases: "(y = z \<and> B =a C) \<or> (y \<noteq> z \<and> B =a [y \<leftrightarrow> z] \<cdot> C \<and> y \<notin> ptrm_fvs C)"
        using fnE `Y =a Z` `Y = PFn y T B` by metis

      consider
        "x = y" "A =a B" and "y = z" "B =a C"
      | "x = y" "A =a B" and "y \<noteq> z" "B =a [y \<leftrightarrow> z] \<cdot> C" "y \<notin> ptrm_fvs C"
      | "x \<noteq> y" "A =a [x \<leftrightarrow> y] \<cdot> B" "x \<notin> ptrm_fvs B" and "y = z" "B =a C"
      | "x \<noteq> y" "A =a [x \<leftrightarrow> y] \<cdot> B" "x \<notin> ptrm_fvs B" and "y \<noteq> z" "B =a [y \<leftrightarrow> z] \<cdot> C" "y \<notin> ptrm_fvs C" and "x = z"
      | "x \<noteq> y" "A =a [x \<leftrightarrow> y] \<cdot> B" "x \<notin> ptrm_fvs B" and "y \<noteq> z" "B =a [y \<leftrightarrow> z] \<cdot> C" "y \<notin> ptrm_fvs C" and "x \<noteq> z"
        using Y_cases Z_cases by auto

      thus ?thesis proof(cases)
        case 1
          have "A =a C" using `A =a B` `B =a C` IH * by metis
          have "x = z" using `x = y` `y = z` by metis
          show ?thesis using `A =a C` `x = z` X Z
            using ptrm_alpha_equiv.fn1 by metis
        next
        case 2
          have "x \<noteq> z" using `x = y` `y \<noteq> z` by metis
          have "A =a [x \<leftrightarrow> z] \<cdot> C" using `A =a B` `B =a [y \<leftrightarrow> z] \<cdot> C` `x = y` IH * by metis
          have "x \<notin> ptrm_fvs C" using `x = y` `y \<notin> ptrm_fvs C` by metis
          thus ?thesis using `x \<noteq> z` `A =a [x \<leftrightarrow> z] \<cdot> C` `x \<notin> ptrm_fvs C` X Z
            using ptrm_alpha_equiv.fn2 by metis
        next
        case 3
          have "x \<noteq> z" using `x \<noteq> y` `y = z` by metis
          have "[x \<leftrightarrow> y] \<cdot> B =a [x \<leftrightarrow> y] \<cdot> C" using `B =a C` ptrm_alpha_equiv_prm by metis
          have "A =a [x \<leftrightarrow> z] \<cdot> C"
            using `A =a [x \<leftrightarrow> y] \<cdot> B` `[x \<leftrightarrow> y] \<cdot> B =a [x \<leftrightarrow> y] \<cdot> C` `y = z` IH *
            by metis
          have "x \<notin> ptrm_fvs C" using `B =a C` `x \<notin> ptrm_fvs B` ptrm_alpha_equiv_fvs by metis
          thus ?thesis using `x \<noteq> z` `A =a [x \<leftrightarrow> z] \<cdot> C` `x \<notin> ptrm_fvs C` X Z
            using ptrm_alpha_equiv.fn2 by metis
        next
        case 4
          have "[x \<leftrightarrow> y] \<cdot> B =a [x \<leftrightarrow> y] \<cdot> [y \<leftrightarrow> z] \<cdot> C"
            using `B =a [y \<leftrightarrow> z] \<cdot> C` ptrm_alpha_equiv_prm by metis
          hence "A =a [x \<leftrightarrow> y] \<cdot> [y \<leftrightarrow> z] \<cdot> C"
            using `A =a [x \<leftrightarrow> y] \<cdot> B` IH * by metis
          hence "A =a ([x \<leftrightarrow> y] \<diamondop> [y \<leftrightarrow> z]) \<cdot> C" using ptrm_prm_apply_compose by metis
          hence "A =a ([x \<leftrightarrow> y] \<diamondop> [y \<leftrightarrow> x]) \<cdot> C" using `x = z` by metis
          hence "A =a ([x \<leftrightarrow> y] \<diamondop> [x \<leftrightarrow> y]) \<cdot> C" using prm_unit_commutes by metis
          hence "A =a \<epsilon> \<cdot> C" using `x = z` prm_unit_involution by metis
          hence "A =a C" using ptrm_prm_apply_id by metis

          thus ?thesis using `x = z` `A =a C` X Z
            using ptrm_alpha_equiv.fn1 by metis
        next
        case 5
          have "x \<notin> ptrm_fvs C" proof -
            have "ptrm_fvs B = ptrm_fvs ([y \<leftrightarrow> z] \<cdot> C)"
              using ptrm_alpha_equiv_fvs `B =a [y \<leftrightarrow> z] \<cdot> C` by metis
            hence "x \<notin> ptrm_fvs ([y \<leftrightarrow> z] \<cdot> C)" using `x \<notin> ptrm_fvs B` by auto
            hence "x \<notin> [y \<leftrightarrow> z] {$} ptrm_fvs C" using ptrm_prm_fvs by metis
            consider "z \<in> ptrm_fvs C" | "z \<notin> ptrm_fvs C" by auto
            thus ?thesis proof(cases)
              case 1
                hence "[y \<leftrightarrow> z] {$} ptrm_fvs C = ptrm_fvs C - {z} \<union> {y}"
                  using prm_set_unit_action prm_unit_commutes
                  and `z \<in> ptrm_fvs C` `y \<notin> ptrm_fvs C` by metis
                hence "x \<notin> ptrm_fvs C - {z} \<union> {y}" using `x \<notin> [y \<leftrightarrow> z] {$} ptrm_fvs C` by auto
                hence "x \<notin> ptrm_fvs C - {z}" using `x \<noteq> y` by auto
                thus ?thesis using `x \<noteq> z` by auto
              next
              case 2
                hence "[y \<leftrightarrow> z] {$} ptrm_fvs C = ptrm_fvs C" using prm_set_unit_inaction `y \<notin> ptrm_fvs C` by metis
                thus ?thesis using `x \<notin> [y \<leftrightarrow> z] {$} ptrm_fvs C` by auto
              next
            qed
          qed

          have "A =a [x \<leftrightarrow> z] \<cdot> C" proof -
            have "A =a ([x \<leftrightarrow> y] \<diamondop> [y \<leftrightarrow> z]) \<cdot> C"
              using IH * `A =a [x \<leftrightarrow> y] \<cdot> B` `B =a [y \<leftrightarrow> z] \<cdot> C`
              and ptrm_alpha_equiv_prm ptrm_prm_apply_compose by metis

            have "([x \<leftrightarrow> y] \<diamondop> [y \<leftrightarrow> z]) \<cdot> C =a [x \<leftrightarrow> z] \<cdot> C" proof -
              have "prm_disagreement ([x \<leftrightarrow> y] \<diamondop> [y \<leftrightarrow> z]) [x \<leftrightarrow> z] = {x, y}"
                using `x \<noteq> y` `y \<noteq> z` `x \<noteq> z` prm_disagreement_composition by metis

              hence "\<And>a. a \<in> prm_disagreement ([x \<leftrightarrow> y] \<diamondop> [y \<leftrightarrow> z]) [x \<leftrightarrow> z] \<Longrightarrow> a \<notin> ptrm_fvs C"
                using `x \<notin> ptrm_fvs C` `y \<notin> ptrm_fvs C`
                using Diff_iff Diff_insert_absorb insert_iff by auto
              thus ?thesis using ptrm_prm_agreement_equiv by metis
            qed

            thus ?thesis using IH *
              using `A =a ([x \<leftrightarrow> y] \<diamondop> [y \<leftrightarrow> z]) \<cdot> C` `([x \<leftrightarrow> y] \<diamondop> [y \<leftrightarrow> z]) \<cdot> C =a [x \<leftrightarrow> z] \<cdot> C`
              by metis
          qed

          show ?thesis using `x \<noteq> z` `A =a [x \<leftrightarrow> z] \<cdot> C` `x \<notin> ptrm_fvs C` X Z
            using ptrm_alpha_equiv.fn2 by metis
        next
      qed
    next
  qed
qed

corollary ptrm_alpha_equiv_transp:
  shows "transp ptrm_alpha_equiv"
unfolding transp_def using ptrm_alpha_equiv_transitive by auto

end
