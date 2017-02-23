theory PreSimplyTyped
imports Main Fresh Permutation
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

fun ptrm_apply_prm :: "'a prm \<Rightarrow> 'a ptrm \<Rightarrow> 'a ptrm" (infixr "\<bullet>" 150) where
  "ptrm_apply_prm \<pi> (PVar x) = PVar (\<pi> $ x)"
| "ptrm_apply_prm \<pi> (PApp A B) = PApp (ptrm_apply_prm \<pi> A) (ptrm_apply_prm \<pi> B)"
| "ptrm_apply_prm \<pi> (PFn x T A) = PFn (\<pi> $ x) T (ptrm_apply_prm \<pi> A)"

inductive ptrm_alpha_equiv :: "'a ptrm \<Rightarrow> 'a ptrm \<Rightarrow> bool" (infix "\<approx>" 100) where
  var:        "(PVar x) \<approx> (PVar x)"
| app:        "\<lbrakk>A \<approx> B; C \<approx> D\<rbrakk> \<Longrightarrow> (PApp A C) \<approx> (PApp B D)"
| fn1:        "A \<approx> B \<Longrightarrow> (PFn x T A) \<approx> (PFn x T B)"
| fn2:        "\<lbrakk>a \<noteq> b; A \<approx> [a \<leftrightarrow> b] \<bullet> B; a \<notin> ptrm_fvs B\<rbrakk> \<Longrightarrow> (PFn a T A) \<approx> (PFn b T B)"

inductive_cases varE: "PVar x \<approx> Y"
inductive_cases appE: "PApp A B \<approx> Y"
inductive_cases fnE:  "PFn x T A \<approx> Y"

lemma ptrm_prm_apply_id:
  shows "\<epsilon> \<bullet> X = X"
by(induction X, simp_all add: prm_apply_id)

lemma ptrm_prm_apply_compose:
  shows "\<pi> \<bullet> \<sigma> \<bullet> X = (\<pi> \<diamondop> \<sigma>) \<bullet> X"
by(induction X, simp_all add: prm_apply_composition)

lemma ptrm_size_prm:
  shows "size X = size (\<pi> \<bullet> X)"
by(induction X, auto)

lemma ptrm_size_alpha_equiv:
  assumes "X \<approx> Y"
  shows "size X = size Y"
using assms proof(induction rule: ptrm_alpha_equiv.induct, simp, simp, simp)
  case (fn2 a b A B T)
    hence "size A = size B" using ptrm_size_prm by metis
    thus ?case by auto
  next
qed

lemma ptrm_fvs_finite:
  shows "finite (ptrm_fvs X)"
by(induction X, auto)

lemma ptrm_prm_fvs:
  shows "ptrm_fvs (\<pi> \<bullet> X) = \<pi> {$} ptrm_fvs X"
proof(induction X)
  case (PVar x)
    have "ptrm_fvs (\<pi> \<bullet> PVar x) = ptrm_fvs (PVar (\<pi> $ x))" by simp
    moreover have "... = {\<pi> $ x}" by simp
    moreover have "... = \<pi> {$} {x}" using prm_set_singleton by metis
    moreover have "... = \<pi> {$} ptrm_fvs (PVar x)" by simp
    ultimately show ?case by metis
  next
  case (PApp A B)
    have "ptrm_fvs (\<pi> \<bullet> PApp A B) = ptrm_fvs (PApp (\<pi> \<bullet> A) (\<pi> \<bullet> B))" by simp
    moreover have "... = ptrm_fvs (\<pi> \<bullet> A) \<union> ptrm_fvs (\<pi> \<bullet> B)" by simp
    moreover have "... = \<pi> {$} ptrm_fvs A \<union> \<pi> {$} ptrm_fvs B" using PApp.IH by metis
    moreover have "... = \<pi> {$} (ptrm_fvs A \<union> ptrm_fvs B)" using prm_set_distributes_union by metis
    moreover have "... = \<pi> {$} ptrm_fvs (PApp A B)" by simp
    ultimately show ?case by metis
  next
  case (PFn x T A)
    have "ptrm_fvs (\<pi> \<bullet> PFn x T A) = ptrm_fvs (PFn (\<pi> $ x) T (\<pi> \<bullet> A))" by simp
    moreover have "... = ptrm_fvs (\<pi> \<bullet> A) - {\<pi> $ x}" by simp
    moreover have "... = \<pi> {$} ptrm_fvs A - {\<pi> $ x}" using PFn.IH by metis
    moreover have "... = \<pi> {$} ptrm_fvs A - \<pi> {$} {x}" using prm_set_singleton by metis
    moreover have "... = \<pi> {$} (ptrm_fvs A - {x})" using prm_set_distributes_difference by metis
    moreover have "... = \<pi> {$} ptrm_fvs (PFn x T A)" by simp
    ultimately show ?case by metis
  next
qed

lemma ptrm_alpha_equiv_fvs:
  assumes "X \<approx> Y"
  shows "ptrm_fvs X = ptrm_fvs Y"
using assms proof(induction rule: ptrm_alpha_equiv.induct, simp, simp, simp)
  case (fn2 a b A B T)
    have "ptrm_fvs (PFn a T A) = ptrm_fvs A - {a}" by simp
    moreover have "... = ptrm_fvs ([a \<leftrightarrow> b] \<bullet> B) - {a}" using fn2.IH by metis
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
  assumes "X \<approx> Y"
  shows "\<pi> \<bullet> X \<approx> \<pi> \<bullet> Y"
using assms proof(induction rule: ptrm_alpha_equiv.induct)
  case (var x)
    thus ?case using ptrm_alpha_equiv.var by simp
  next
  case (app A B C D)
    thus ?case using ptrm_alpha_equiv.app by simp
  next
  case (fn1 A B x T)
    thus ?case using ptrm_alpha_equiv.fn1 by simp
  next
  case (fn2 a b A B T)
    have "\<pi> $ a \<noteq> \<pi> $ b" using `a \<noteq> b` using prm_apply_unequal by metis
    moreover have "\<pi> $ a \<notin> ptrm_fvs (\<pi> \<bullet> B)" using `a \<notin> ptrm_fvs B`
      using imageE prm_apply_unequal prm_set_def ptrm_prm_fvs by (metis (no_types, lifting))
    moreover have "\<pi> \<bullet> A \<approx> [\<pi> $ a \<leftrightarrow> \<pi> $ b] \<bullet> \<pi> \<bullet> B"
      using fn2.IH prm_compose_push ptrm_prm_apply_compose by metis
    ultimately show ?case using ptrm_alpha_equiv.fn2 by simp
  next
qed

lemma ptrm_swp_transfer:
  assumes "[a \<leftrightarrow> b] \<bullet> X \<approx> Y"
  shows "X \<approx> [a \<leftrightarrow> b] \<bullet> Y"
proof -
  have "[a \<leftrightarrow> b] \<bullet> [a \<leftrightarrow> b] \<bullet> X \<approx> [a \<leftrightarrow> b] \<bullet> Y"
    using assms ptrm_alpha_equiv_prm by metis
  hence "([a \<leftrightarrow> b] \<diamondop> [a \<leftrightarrow> b]) \<bullet> X \<approx> [a \<leftrightarrow> b] \<bullet> Y" using ptrm_prm_apply_compose
    by metis
  hence "\<epsilon> \<bullet> X \<approx> [a \<leftrightarrow> b] \<bullet> Y" using prm_unit_involution by metis
  thus ?thesis using ptrm_prm_apply_id by metis
qed

lemma ptrm_fresh_transfer:
  assumes "a \<noteq> b" "a \<notin> ptrm_fvs A"
  shows "b \<notin> ptrm_fvs ([a \<leftrightarrow> b] \<bullet> A)"
using assms proof(induction A)
  case (PVar x)
    hence "a \<noteq> x" by auto
    consider "b = x" | "b \<noteq> x" by auto
    thus ?case proof(cases)
      assume "b = x"
      hence "[a \<leftrightarrow> b] \<bullet> PVar x = PVar a"
        using prm_unit_action prm_unit_commutes ptrm_apply_prm.simps(1) by metis
      hence "ptrm_fvs ([a \<leftrightarrow> b] \<bullet> PVar x) = {a}" by simp
      thus ?thesis using `a \<noteq> x` `b = x` by simp
      next

      assume "b \<noteq> x"
      hence "[a \<leftrightarrow> b] \<bullet> PVar x = PVar x"
        using prm_unit_inaction `a \<noteq> x` ptrm_apply_prm.simps(1) by metis
      hence "ptrm_fvs ([a \<leftrightarrow> b] \<bullet> PVar x) = {x}" by simp
      thus ?thesis using `b \<noteq> x` by simp
    qed
  next
  case (PApp A B)
    hence "a \<noteq> b" "a \<notin> ptrm_fvs A" "a \<notin> ptrm_fvs B" by auto
    hence "b \<notin> ptrm_fvs ([a \<leftrightarrow> b] \<bullet> A)" "b \<notin> ptrm_fvs ([a \<leftrightarrow> b] \<bullet> B)" using PApp.IH by auto
    hence "b \<notin> ptrm_fvs (PApp ([a \<leftrightarrow> b] \<bullet> A) ([a \<leftrightarrow> b] \<bullet> B))" by simp
    thus ?case by simp
  next
  case (PFn x T A)
    consider "a = x" | "a \<notin> ptrm_fvs A \<and> a \<noteq> x" using PFn.prems by auto
    thus ?case proof(cases)
      assume "a = x"
      hence "[a \<leftrightarrow> b] \<bullet> PFn x T A = PFn b T ([a \<leftrightarrow> b] \<bullet> A)" using prm_unit_action by simp
      thus ?thesis by simp
      next

      assume "a \<notin> ptrm_fvs A \<and> a \<noteq> x"
      hence "a \<notin> ptrm_fvs A" "a \<noteq> x" by auto
      hence *: "b \<notin> ptrm_fvs ([a \<leftrightarrow> b] \<bullet> A)" using PFn by auto

      consider "b = x" | "b \<noteq> x" by auto
      thus ?thesis proof(cases)
        assume "b = x"
        hence "[a \<leftrightarrow> b] \<bullet> PFn x T A = PFn a T ([a \<leftrightarrow> b] \<bullet> A)"
          using prm_unit_action prm_unit_commutes ptrm_apply_prm.simps(3) by metis
        hence "ptrm_fvs ([a \<leftrightarrow> b] \<bullet> PFn x T A) = ptrm_fvs ([a \<leftrightarrow> b] \<bullet> A) - {a}" by simp
        thus ?thesis using `a \<noteq> x` `b = x` * by auto
        next

        assume "b \<noteq> x"
        hence "[a \<leftrightarrow> b] \<bullet> PFn x T A = PFn x T ([a \<leftrightarrow> b] \<bullet> A)"
          using `a \<noteq> x` prm_unit_inaction ptrm_apply_prm.simps(3) by metis
        hence "ptrm_fvs ([a \<leftrightarrow> b] \<bullet> PFn x T A) = ptrm_fvs ([a \<leftrightarrow> b] \<bullet> A) - {x}" by simp
        thus ?thesis using `b \<noteq> x` * by auto
      qed
    qed
  next
qed

lemma ptrm_alpha_equiv_fvs_transfer:
  assumes "A \<approx> [a \<leftrightarrow> b] \<bullet> B" and "a \<notin> ptrm_fvs B"
  shows "b \<notin> ptrm_fvs A"
proof(cases "a = b")
  assume "a = b"
  hence "A \<approx> B" using prm_unit_equal_id ptrm_prm_apply_id assms(1) by metis
  hence "ptrm_fvs A = ptrm_fvs B" using ptrm_alpha_equiv_fvs by auto
  thus ?thesis using `a = b` assms(2) by auto
  next

  assume "a \<noteq> b"
  thus ?thesis proof(cases "b \<in> ptrm_fvs B")
    case True
      have *: "b \<notin> ptrm_fvs B - {b} \<union> {a}" using assms `a \<noteq> b` by simp
      have "ptrm_fvs A = ptrm_fvs ([a \<leftrightarrow> b] \<bullet> B)" using ptrm_alpha_equiv_fvs assms by metis
      moreover have "... = [a \<leftrightarrow> b] {$} ptrm_fvs B" using ptrm_prm_fvs by metis
      moreover have "... = [b \<leftrightarrow> a] {$} ptrm_fvs B" using prm_unit_commutes by metis
      moreover have "... = ptrm_fvs B - {b} \<union> {a}" using prm_set_unit_action `a \<notin> ptrm_fvs B` `b \<in> ptrm_fvs B` by metis
      ultimately have "ptrm_fvs A = ptrm_fvs B - {b} \<union> {a}" by metis
      thus ?thesis using * by auto
      next
    case False
      have "ptrm_fvs A = ptrm_fvs ([a \<leftrightarrow> b] \<bullet> B)" using ptrm_alpha_equiv_fvs assms by metis
      moreover have "ptrm_fvs ([a \<leftrightarrow> b] \<bullet> B) = [a \<leftrightarrow> b] {$} ptrm_fvs B" using ptrm_prm_fvs by metis
      moreover have "... = ptrm_fvs B" using prm_set_unit_inaction `a \<notin> ptrm_fvs B` `b \<notin> ptrm_fvs B` by metis
      ultimately have "ptrm_fvs A = ptrm_fvs B" by metis
      thus ?thesis using `b \<notin> ptrm_fvs B` by auto
    next
  qed
qed

lemma ptrm_prm_agreement_equiv:
  assumes "\<And>a. a \<in> ds \<pi> \<sigma> \<Longrightarrow> a \<notin> ptrm_fvs M"
  shows "\<pi> \<bullet> M \<approx> \<sigma> \<bullet> M"
using assms proof(induction M arbitrary: \<pi> \<sigma>)
  case (PVar x)
    consider "x \<in> ds \<pi> \<sigma>" | "x \<notin> ds \<pi> \<sigma>" by auto
    thus ?case proof(cases)
      case 1
        hence "x \<notin> ptrm_fvs (PVar x)" using PVar.prems by blast
        thus ?thesis by simp
      next
      case 2
        hence "\<pi> $ x = \<sigma> $ x" using prm_disagreement_ext by metis
        thus ?thesis using ptrm_alpha_equiv.var by simp
      next
    qed
  next
  case (PApp A B)
    hence "\<pi> \<bullet> A \<approx> \<sigma> \<bullet> A" and "\<pi> \<bullet> B \<approx> \<sigma> \<bullet> B" by auto
    thus ?case using ptrm_alpha_equiv.app by auto
  next
  case (PFn x T A)
    consider "x \<notin> ds \<pi> \<sigma>" | "x \<in> ds \<pi> \<sigma>" by auto
    thus ?case proof(cases)
      case 1
        hence *: "\<pi> $ x = \<sigma> $ x" using prm_disagreement_ext by metis
        have "\<And>a. a \<in> ds \<pi> \<sigma> \<Longrightarrow> a \<notin> ptrm_fvs A"
        proof -
          fix a
          assume "a \<in> ds \<pi> \<sigma>"
          hence "a \<notin> ptrm_fvs (PFn x T A)" using PFn.prems by metis
          hence "a = x \<or> a \<notin> ptrm_fvs A" by auto
          thus "a \<notin> ptrm_fvs A" using `a \<in> ds \<pi> \<sigma>` `x \<notin> ds \<pi> \<sigma>` by auto
        qed
        thus ?thesis using PFn.IH * ptrm_alpha_equiv.fn1 ptrm_apply_prm.simps(3) by fastforce
      next
      case 2
        hence "\<pi> $ x \<noteq> \<sigma> $ x" using prm_disagreement_def CollectD by fastforce
        moreover hence "\<pi> $ x \<notin> ptrm_fvs (\<sigma> \<bullet> A)"
          using ptrm_fvs.simps(3) ptrm_prm_fvs prm_set_def prm_disagreement_ext prm_apply_unequal
          using PFn 2 Diff_empty Diff_insert0 image_iff insertE insert_Diff by smt
        moreover have "\<pi> \<bullet> A \<approx> [\<pi> $ x \<leftrightarrow> \<sigma> $ x] \<bullet> \<sigma> \<bullet> A"
        proof -
          have "\<And>a. a \<in> ds \<pi> ([\<pi> $ x \<leftrightarrow> \<sigma> $ x] \<diamondop> \<sigma>) \<Longrightarrow> a \<notin> ptrm_fvs A" proof -
            fix a
            assume *: "a \<in> ds \<pi> ([\<pi> $ x \<leftrightarrow> \<sigma> $ x] \<diamondop> \<sigma>)"
            hence "a \<noteq> x" using `\<pi> $ x \<noteq> \<sigma> $ x`
              using prm_apply_composition prm_disagreement_ext prm_unit_action prm_unit_commutes
              by metis
            hence "a \<in> ds \<pi> \<sigma>"
              using * prm_apply_composition prm_apply_unequal prm_disagreement_ext prm_unit_inaction
              by metis
            thus "a \<notin> ptrm_fvs A" using `a \<noteq> x` PFn.prems by auto
          qed
          thus ?thesis using PFn by (simp add: ptrm_prm_apply_compose)
        qed
        ultimately show ?thesis using ptrm_alpha_equiv.fn2 by simp
      next
    qed
  next
qed

lemma ptrm_prm_unit_inaction:
  assumes "a \<notin> ptrm_fvs X" "b \<notin> ptrm_fvs X"
  shows "[a \<leftrightarrow> b] \<bullet> X \<approx> X"
proof -
  have "(\<And>x. x \<in> ds [a \<leftrightarrow> b] \<epsilon> \<Longrightarrow> x \<notin> ptrm_fvs X)"
  proof -
    fix x
    assume "x \<in> ds [a \<leftrightarrow> b] \<epsilon>"
    hence "[a \<leftrightarrow> b] $ x \<noteq> \<epsilon> $ x"
      unfolding prm_disagreement_def
      by auto
    hence "x = a \<or> x = b"
      using prm_apply_id prm_unit_inaction by metis
    thus "x \<notin> ptrm_fvs X" using assms by auto
  qed
  hence "[a \<leftrightarrow> b] \<bullet> X \<approx> \<epsilon> \<bullet> X"
    using ptrm_prm_agreement_equiv by metis
  thus ?thesis using ptrm_prm_apply_id by metis
qed

lemma ptrm_alpha_equiv_reflexive:
  shows "M \<approx> M"
by(induction M, auto simp add: ptrm_alpha_equiv.intros)

corollary ptrm_alpha_equiv_reflp:
  shows "reflp ptrm_alpha_equiv"
unfolding reflp_def using ptrm_alpha_equiv_reflexive by auto

lemma ptrm_alpha_equiv_symmetric:
  assumes "X \<approx> Y"
  shows "Y \<approx> X"
using assms proof(induction rule: ptrm_alpha_equiv.induct, auto simp add: ptrm_alpha_equiv.intros)
  case (fn2 a b A B T)
    have "b \<noteq> a" using `a \<noteq> b` by auto
    have "B \<approx> [b \<leftrightarrow> a] \<bullet> A" using `[a \<leftrightarrow> b] \<bullet> B \<approx> A`
      using ptrm_swp_transfer prm_unit_commutes by metis

    have "b \<notin> ptrm_fvs A" using `a \<notin> ptrm_fvs B` `A \<approx> [a \<leftrightarrow> b] \<bullet> B` `a \<noteq> b`
      using ptrm_alpha_equiv_fvs_transfer by metis

    show ?case using `b \<noteq> a` `B \<approx> [b \<leftrightarrow> a] \<bullet> A` `b \<notin> ptrm_fvs A`
      using ptrm_alpha_equiv.fn2 by metis
  next
qed

corollary ptrm_alpha_equiv_symp:
  shows "symp ptrm_alpha_equiv"
unfolding symp_def using ptrm_alpha_equiv_symmetric by auto

lemma ptrm_alpha_equiv_transitive:
  assumes "X \<approx> Y" and "Y \<approx> Z"
  shows "X \<approx> Z"
using assms proof(induction "size X" arbitrary: X Y Z rule: less_induct)
  fix X Y Z :: "'a ptrm"
  assume IH: "\<And>K Y Z :: 'a ptrm. size K < size X \<Longrightarrow> K \<approx> Y \<Longrightarrow> Y \<approx> Z \<Longrightarrow> K \<approx> Z"
  assume "X \<approx> Y" and "Y \<approx> Z"
  show "X \<approx> Z" proof(cases X)
    case (PVar x)
      hence "PVar x \<approx> Y" using `X \<approx> Y` by auto
      hence "Y = PVar x" using varE by metis
      hence "PVar x \<approx> Z" using `Y \<approx> Z` by auto
      hence "Z = PVar x" using varE by metis
      thus ?thesis using ptrm_alpha_equiv.var `X = PVar x` by metis
    next
    case (PApp A B)
      obtain C D where "Y = PApp C D" and "A \<approx> C" and "B \<approx> D"
        using appE `X = PApp A B` `X \<approx> Y` by metis
      hence "PApp C D \<approx> Z" using `Y \<approx> Z` by simp
      from this obtain E F where "Z = PApp E F" and "C \<approx> E" and "D \<approx> F" using appE by metis

      have "size A < size X" and "size B < size X" using `X = PApp A B` by auto
      hence "A \<approx> E" and "B \<approx> F" using IH `A \<approx> C` `C \<approx> E` `B \<approx> D` `D \<approx> F` by auto
      thus ?thesis using `X = PApp A B` `Z = PApp E F` ptrm_alpha_equiv.app by metis
    next
    case (PFn x T A)
      from this have X: "X = PFn x T A".
      hence *: "size A < size X" by auto

      obtain y B where "Y = PFn y T B"
        and Y_cases: "(x = y \<and> A \<approx> B) \<or> (x \<noteq> y \<and> A \<approx> [x \<leftrightarrow> y] \<bullet> B \<and> x \<notin> ptrm_fvs B)"
        using fnE `X \<approx> Y` `X = PFn x T A` by metis
      obtain z C where Z: "Z = PFn z T C"
        and Z_cases: "(y = z \<and> B \<approx> C) \<or> (y \<noteq> z \<and> B \<approx> [y \<leftrightarrow> z] \<bullet> C \<and> y \<notin> ptrm_fvs C)"
        using fnE `Y \<approx> Z` `Y = PFn y T B` by metis

      consider
        "x = y" "A \<approx> B" and "y = z" "B \<approx> C"
      | "x = y" "A \<approx> B" and "y \<noteq> z" "B \<approx> [y \<leftrightarrow> z] \<bullet> C" "y \<notin> ptrm_fvs C"
      | "x \<noteq> y" "A \<approx> [x \<leftrightarrow> y] \<bullet> B" "x \<notin> ptrm_fvs B" and "y = z" "B \<approx> C"
      | "x \<noteq> y" "A \<approx> [x \<leftrightarrow> y] \<bullet> B" "x \<notin> ptrm_fvs B" and "y \<noteq> z" "B \<approx> [y \<leftrightarrow> z] \<bullet> C" "y \<notin> ptrm_fvs C" and "x = z"
      | "x \<noteq> y" "A \<approx> [x \<leftrightarrow> y] \<bullet> B" "x \<notin> ptrm_fvs B" and "y \<noteq> z" "B \<approx> [y \<leftrightarrow> z] \<bullet> C" "y \<notin> ptrm_fvs C" and "x \<noteq> z"
        using Y_cases Z_cases by auto

      thus ?thesis proof(cases)
        case 1
          have "A \<approx> C" using `A \<approx> B` `B \<approx> C` IH * by metis
          have "x = z" using `x = y` `y = z` by metis
          show ?thesis using `A \<approx> C` `x = z` X Z
            using ptrm_alpha_equiv.fn1 by metis
        next
        case 2
          have "x \<noteq> z" using `x = y` `y \<noteq> z` by metis
          have "A \<approx> [x \<leftrightarrow> z] \<bullet> C" using `A \<approx> B` `B \<approx> [y \<leftrightarrow> z] \<bullet> C` `x = y` IH * by metis
          have "x \<notin> ptrm_fvs C" using `x = y` `y \<notin> ptrm_fvs C` by metis
          thus ?thesis using `x \<noteq> z` `A \<approx> [x \<leftrightarrow> z] \<bullet> C` `x \<notin> ptrm_fvs C` X Z
            using ptrm_alpha_equiv.fn2 by metis
        next
        case 3
          have "x \<noteq> z" using `x \<noteq> y` `y = z` by metis
          have "[x \<leftrightarrow> y] \<bullet> B \<approx> [x \<leftrightarrow> y] \<bullet> C" using `B \<approx> C` ptrm_alpha_equiv_prm by metis
          have "A \<approx> [x \<leftrightarrow> z] \<bullet> C"
            using `A \<approx> [x \<leftrightarrow> y] \<bullet> B` `[x \<leftrightarrow> y] \<bullet> B \<approx> [x \<leftrightarrow> y] \<bullet> C` `y = z` IH *
            by metis
          have "x \<notin> ptrm_fvs C" using `B \<approx> C` `x \<notin> ptrm_fvs B` ptrm_alpha_equiv_fvs by metis
          thus ?thesis using `x \<noteq> z` `A \<approx> [x \<leftrightarrow> z] \<bullet> C` `x \<notin> ptrm_fvs C` X Z
            using ptrm_alpha_equiv.fn2 by metis
        next
        case 4
          have "[x \<leftrightarrow> y] \<bullet> B \<approx> [x \<leftrightarrow> y] \<bullet> [y \<leftrightarrow> z] \<bullet> C"
            using `B \<approx> [y \<leftrightarrow> z] \<bullet> C` ptrm_alpha_equiv_prm by metis
          hence "A \<approx> [x \<leftrightarrow> y] \<bullet> [y \<leftrightarrow> z] \<bullet> C"
            using `A \<approx> [x \<leftrightarrow> y] \<bullet> B` IH * by metis
          hence "A \<approx> ([x \<leftrightarrow> y] \<diamondop> [y \<leftrightarrow> z]) \<bullet> C" using ptrm_prm_apply_compose by metis
          hence "A \<approx> ([x \<leftrightarrow> y] \<diamondop> [y \<leftrightarrow> x]) \<bullet> C" using `x = z` by metis
          hence "A \<approx> ([x \<leftrightarrow> y] \<diamondop> [x \<leftrightarrow> y]) \<bullet> C" using prm_unit_commutes by metis
          hence "A \<approx> \<epsilon> \<bullet> C" using `x = z` prm_unit_involution by metis
          hence "A \<approx> C" using ptrm_prm_apply_id by metis

          thus ?thesis using `x = z` `A \<approx> C` X Z
            using ptrm_alpha_equiv.fn1 by metis
        next
        case 5
          have "x \<notin> ptrm_fvs C" proof -
            have "ptrm_fvs B = ptrm_fvs ([y \<leftrightarrow> z] \<bullet> C)"
              using ptrm_alpha_equiv_fvs `B \<approx> [y \<leftrightarrow> z] \<bullet> C` by metis
            hence "x \<notin> ptrm_fvs ([y \<leftrightarrow> z] \<bullet> C)" using `x \<notin> ptrm_fvs B` by auto
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

          have "A \<approx> [x \<leftrightarrow> z] \<bullet> C" proof -
            have "A \<approx> ([x \<leftrightarrow> y] \<diamondop> [y \<leftrightarrow> z]) \<bullet> C"
              using IH * `A \<approx> [x \<leftrightarrow> y] \<bullet> B` `B \<approx> [y \<leftrightarrow> z] \<bullet> C`
              and ptrm_alpha_equiv_prm ptrm_prm_apply_compose by metis

            have "([x \<leftrightarrow> y] \<diamondop> [y \<leftrightarrow> z]) \<bullet> C \<approx> [x \<leftrightarrow> z] \<bullet> C" proof -
              have "ds ([x \<leftrightarrow> y] \<diamondop> [y \<leftrightarrow> z]) [x \<leftrightarrow> z] = {x, y}"
                using `x \<noteq> y` `y \<noteq> z` `x \<noteq> z` prm_disagreement_composition by metis

              hence "\<And>a. a \<in> ds ([x \<leftrightarrow> y] \<diamondop> [y \<leftrightarrow> z]) [x \<leftrightarrow> z] \<Longrightarrow> a \<notin> ptrm_fvs C"
                using `x \<notin> ptrm_fvs C` `y \<notin> ptrm_fvs C`
                using Diff_iff Diff_insert_absorb insert_iff by auto
              thus ?thesis using ptrm_prm_agreement_equiv by metis
            qed

            thus ?thesis using IH *
              using `A \<approx> ([x \<leftrightarrow> y] \<diamondop> [y \<leftrightarrow> z]) \<bullet> C` `([x \<leftrightarrow> y] \<diamondop> [y \<leftrightarrow> z]) \<bullet> C \<approx> [x \<leftrightarrow> z] \<bullet> C`
              by metis
          qed

          show ?thesis using `x \<noteq> z` `A \<approx> [x \<leftrightarrow> z] \<bullet> C` `x \<notin> ptrm_fvs C` X Z
            using ptrm_alpha_equiv.fn2 by metis
        next
      qed
    next
  qed
qed

corollary ptrm_alpha_equiv_transp:
  shows "transp ptrm_alpha_equiv"
unfolding transp_def using ptrm_alpha_equiv_transitive by auto


type_synonym 'a typing_ctx = "'a \<rightharpoonup> type"

fun ptrm_infer_type :: "'a typing_ctx \<Rightarrow> 'a ptrm \<Rightarrow> type option" where
  "ptrm_infer_type \<Gamma> (PVar x) = \<Gamma> x"
| "ptrm_infer_type \<Gamma> (PApp A B) = (case (ptrm_infer_type \<Gamma> A, ptrm_infer_type \<Gamma> B) of
     (Some (TArr \<tau> \<sigma>), Some \<tau>') \<Rightarrow> (if \<tau> = \<tau>' then Some \<sigma> else None)
   | _ \<Rightarrow> None
   )"
| "ptrm_infer_type \<Gamma> (PFn x \<tau> A) = (case ptrm_infer_type (\<Gamma>(x \<mapsto> \<tau>)) A of
     Some \<sigma> \<Rightarrow> Some (TArr \<tau> \<sigma>)
   | None \<Rightarrow> None
   )"

lemma ptrm_infer_type_weaken:
  assumes "y \<notin> ptrm_fvs X"
  shows "ptrm_infer_type \<Gamma> X = ptrm_infer_type (\<Gamma>(y \<mapsto> \<tau>)) X"
using assms proof(induction X arbitrary: \<Gamma>, simp, simp)
  case (PFn x T A)
    consider "y = x" | "y \<noteq> x \<and> y \<notin> ptrm_fvs A" using `y \<notin> ptrm_fvs (PFn x T A)` by auto
    thus ?case proof(cases)
      case 1
        have "\<Gamma>(y \<mapsto> \<tau>)(x \<mapsto> T) = \<Gamma>(x \<mapsto> T)" using `y = x` by simp
        thus ?thesis by (metis ptrm_infer_type.simps(3))
      next
      case 2
        hence "y \<noteq> x" and "y \<notin> ptrm_fvs A" by auto
        hence "\<And>\<Gamma>. ptrm_infer_type \<Gamma> A = ptrm_infer_type (\<Gamma>(y \<mapsto> \<tau>)) A" using PFn.IH by metis
        hence "\<And>\<Gamma>. ptrm_infer_type (\<Gamma>(x \<mapsto> T)) A = ptrm_infer_type (\<Gamma>(x \<mapsto> T)(y \<mapsto> \<tau>)) A"
          by auto
        hence "\<And>\<Gamma>. ptrm_infer_type (\<Gamma>(x \<mapsto> T)) A = ptrm_infer_type (\<Gamma>(y \<mapsto> \<tau>)(x \<mapsto> T)) A"
          using `y \<noteq> x` by simp
        thus ?thesis using ptrm_infer_type.simps(3) by metis
      next
    qed
  next
qed

lemma ptrm_infer_type_swp_types:
  assumes "a \<noteq> b"
  shows "ptrm_infer_type (\<Gamma>(a \<mapsto> T, b \<mapsto> S)) X = ptrm_infer_type (\<Gamma>(a \<mapsto> S, b \<mapsto> T)) ([a \<leftrightarrow> b] \<bullet> X)"
using assms proof(induction X arbitrary: T S \<Gamma>)
  case (PVar x)
    consider "x = a" | "x = b" | "x \<noteq> a \<and> x \<noteq> b" by auto
    thus ?case proof(cases)
      assume "x = a"
      thus ?thesis using `a \<noteq> b` by (simp add: prm_unit_action)
      next

      assume "x = b"
      thus ?thesis using `a \<noteq> b`
        using prm_unit_action prm_unit_commutes fun_upd_same fun_upd_twist
        by (metis ptrm_apply_prm.simps(1) ptrm_infer_type.simps(1))
      next

      assume "x \<noteq> a \<and> x \<noteq> b"
      thus ?thesis by (simp add: prm_unit_inaction)
      next
    qed
  next
  case (PApp A B)
    thus ?case by simp
  next
  case (PFn x \<tau> A)
    hence *:
      "\<And>T S \<Gamma>. ptrm_infer_type (\<Gamma>(a \<mapsto> T, b \<mapsto> S)) A = ptrm_infer_type (\<Gamma>(a \<mapsto> S, b \<mapsto> T)) ([a \<leftrightarrow> b] \<bullet> A)"
      by metis

    consider "x = a" | "x = b" | "x \<noteq> a \<and> x \<noteq> b" by auto
    thus ?case proof(cases)
      assume "x = a"
      thus ?thesis
        using * fun_upd_twist fun_upd_upd prm_unit_action
        using ptrm_apply_prm.simps(3) ptrm_infer_type.simps(3)
        by smt
      next

      assume "x = b"
      thus ?thesis
        using * fun_upd_twist fun_upd_upd prm_unit_action prm_unit_commutes
        using ptrm_apply_prm.simps(3) ptrm_infer_type.simps(3)
        by smt
      next

      assume "x \<noteq> a \<and> x \<noteq> b"
      thus ?thesis
        using * fun_upd_twist prm_unit_inaction
        using ptrm_apply_prm.simps(3) ptrm_infer_type.simps(3)
        by smt
      next
    qed
  next
qed

lemma ptrm_infer_type_swp:
  assumes "a \<noteq> b" "b \<notin> ptrm_fvs X"
  shows "ptrm_infer_type (\<Gamma>(a \<mapsto> \<tau>)) X = ptrm_infer_type (\<Gamma>(b \<mapsto> \<tau>)) ([a \<leftrightarrow> b] \<bullet> X)"
using assms proof(induction X arbitrary: \<tau> \<Gamma>)
  case (PVar x)
    hence "x \<noteq> b" by simp
    consider "x = a" | "x \<noteq> a" by auto
    thus ?case proof(cases)
      assume "x = a"
      hence "[a \<leftrightarrow> b] \<bullet> (PVar x) = PVar b"
      and   "ptrm_infer_type (\<Gamma>(a \<mapsto> \<tau>)) (PVar x) = Some \<tau>" using prm_unit_action by auto
      thus ?thesis by auto
      next

      assume "x \<noteq> a"
      hence *: "[a \<leftrightarrow> b] \<bullet> PVar x = PVar x" using `x \<noteq> b` prm_unit_inaction by simp
      consider "\<exists>\<sigma>. \<Gamma> x = Some \<sigma>" | "\<Gamma> x = None" by auto
      thus ?thesis proof(cases)
        assume "\<exists>\<sigma>. \<Gamma> x = Some \<sigma>"
        from this obtain \<sigma> where "\<Gamma> x = Some \<sigma>" by auto
        thus ?thesis using * `x \<noteq> a` `x \<noteq> b` by auto
        next

        assume "\<Gamma> x = None"
        thus ?thesis using * `x \<noteq> a` `x \<noteq> b` by auto
      qed
    qed
  next
  case (PApp A B)
    have "b \<notin> ptrm_fvs A" and "b \<notin> ptrm_fvs B" using PApp.prems by auto
    hence "ptrm_infer_type (\<Gamma>(a \<mapsto> \<tau>)) A = ptrm_infer_type (\<Gamma>(b \<mapsto> \<tau>)) ([a \<leftrightarrow> b] \<bullet> A)"
    and   "ptrm_infer_type (\<Gamma>(a \<mapsto> \<tau>)) B = ptrm_infer_type (\<Gamma>(b \<mapsto> \<tau>)) ([a \<leftrightarrow> b] \<bullet> B)"
      using PApp.IH assms by metis+
    
    thus ?case by (metis ptrm_apply_prm.simps(2) ptrm_infer_type.simps(2))
  next
  case (PFn x \<sigma> A)
    consider "b \<noteq> x \<and> b \<notin> ptrm_fvs A" | "b = x" using PFn.prems by auto
    thus ?case proof(cases)
      assume "b \<noteq> x \<and> b \<notin> ptrm_fvs A"
      hence "b \<noteq> x" "b \<notin> ptrm_fvs A" by auto
      hence *: "\<And>\<tau> \<Gamma>. ptrm_infer_type (\<Gamma>(a \<mapsto> \<tau>)) A = ptrm_infer_type (\<Gamma>(b \<mapsto> \<tau>)) ([a \<leftrightarrow> b] \<bullet> A)"
        using PFn.IH assms by metis
      consider "a = x" | "a \<noteq> x" by auto
      thus ?thesis proof(cases)
        assume "a = x"
        hence "ptrm_infer_type (\<Gamma>(a \<mapsto> \<tau>)) (PFn x \<sigma> A) = ptrm_infer_type (\<Gamma>(a \<mapsto> \<tau>)) (PFn a \<sigma> A)"
        and "
          ptrm_infer_type (\<Gamma>(b \<mapsto> \<tau>)) ([a \<leftrightarrow> b] \<bullet> PFn x \<sigma> A) =
          ptrm_infer_type (\<Gamma>(b \<mapsto> \<tau>)) (PFn b \<sigma> ([a \<leftrightarrow> b] \<bullet> A))"
        by (auto simp add: prm_unit_action)
        thus ?thesis using * ptrm_infer_type.simps(3) fun_upd_upd by metis
        next

        assume "a \<noteq> x"
        thus ?thesis
          using `b \<noteq> x` prm_unit_inaction * fun_upd_twist
          using ptrm_apply_prm.simps(3) ptrm_infer_type.simps(3)
          by smt
        next
      qed
      next

      assume "b = x"
      hence "a \<noteq> x" using assms by auto
      have "
        ptrm_infer_type (\<Gamma>(a \<mapsto> \<tau>)(b \<mapsto> \<sigma>)) A =
        ptrm_infer_type (\<Gamma>(b \<mapsto> \<tau>)(a \<mapsto> \<sigma>)) ([a \<leftrightarrow> b] \<bullet> A)
      " using ptrm_infer_type_swp_types using `a \<noteq> b` fun_upd_twist by metis
      thus ?thesis
        using `b = x` prm_unit_action prm_unit_commutes
        using ptrm_infer_type.simps(3) ptrm_apply_prm.simps(3) by metis
      next
    qed
  next
qed

lemma ptrm_infer_type_alpha_equiv:
  assumes "X \<approx> Y"
  shows "ptrm_infer_type \<Gamma> X = ptrm_infer_type \<Gamma> Y"
using assms proof(induction arbitrary: \<Gamma>, simp, simp, simp)
  case (fn2 a b A B T \<Gamma>)
    hence "ptrm_infer_type (\<Gamma>(a \<mapsto> T)) A = ptrm_infer_type (\<Gamma>(b \<mapsto> T)) B"
      using ptrm_infer_type_swp prm_unit_commutes by metis
    thus ?case by simp
  next
qed

end
