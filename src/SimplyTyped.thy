theory SimplyTyped
imports Main Permutation Fresh PreSimplyTyped
begin

quotient_type 'a trm = "'a ptrm" / ptrm_alpha_equiv
proof(rule equivpI)
  show "reflp  ptrm_alpha_equiv" using ptrm_alpha_equiv_reflp.
  show "symp   ptrm_alpha_equiv" using ptrm_alpha_equiv_symp.
  show "transp ptrm_alpha_equiv" using ptrm_alpha_equiv_transp.
qed

lift_definition Unit :: "'a trm" is PUnit.
lift_definition Var :: "'a \<Rightarrow> 'a trm" is PVar.
lift_definition App :: "'a trm \<Rightarrow> 'a trm \<Rightarrow> 'a trm" is PApp using ptrm_alpha_equiv.app.
lift_definition Fn  :: "'a \<Rightarrow> type \<Rightarrow> 'a trm \<Rightarrow> 'a trm" is PFn using ptrm_alpha_equiv.fn1.
lift_definition Pair :: "'a trm \<Rightarrow> 'a trm \<Rightarrow> 'a trm" is PPair using ptrm_alpha_equiv.pair.
lift_definition Fst :: "'a trm \<Rightarrow> 'a trm" is PFst using ptrm_alpha_equiv.fst.
lift_definition Snd :: "'a trm \<Rightarrow> 'a trm" is PSnd using ptrm_alpha_equiv.snd.
lift_definition fvs :: "'a trm \<Rightarrow> 'a set" is ptrm_fvs using ptrm_alpha_equiv_fvs.
lift_definition prm :: "'a prm \<Rightarrow> 'a trm \<Rightarrow> 'a trm" (infixr "\<cdot>" 150) is ptrm_apply_prm
  using ptrm_alpha_equiv_prm.
lift_definition depth :: "'a trm \<Rightarrow> nat" is size using ptrm_size_alpha_equiv.

lemma depth_app:
  shows "depth A < depth (App A B)" "depth B < depth (App A B)"
by(transfer, auto)+

lemma depth_fn:
  shows "depth A < depth (Fn x T A)"
by(transfer, auto)

lemma unit_not_var:
  shows "Unit \<noteq> Var x"
proof(transfer)
  fix x :: 'a
  show "\<not> PUnit \<approx> PVar x"
  proof(rule classical)
    assume "\<not>\<not> PUnit \<approx> PVar x"
    hence False using unitE by fastforce
    thus ?thesis by blast
  qed
qed

lemma unit_not_app:
  shows "Unit \<noteq> App A B"
proof(transfer)
  fix A B :: "'a ptrm"
  show "\<not> PUnit \<approx> PApp A B"
  proof(rule classical)
    assume "\<not>\<not> PUnit \<approx> PApp A B"
    hence False using unitE by fastforce
    thus ?thesis by blast
  qed
qed

lemma unit_not_fn:
  shows "Unit \<noteq> Fn x T A"
proof(transfer)
  fix x :: 'a and T A
  show "\<not> PUnit \<approx> PFn x T A"
  proof(rule classical)
    assume "\<not>\<not> PUnit \<approx> PFn x T A"
    hence False using unitE by fastforce
    thus ?thesis by blast
  qed
qed

lemma unit_not_pair:
  shows "Unit \<noteq> Pair A B"
proof(transfer)
  fix A B :: "'a ptrm"
  show "\<not> PUnit \<approx> PPair A B"
  proof(rule classical)
    assume "\<not>\<not> PUnit \<approx> PPair A B"
    hence False using unitE by fastforce
    thus ?thesis by blast
  qed
qed

lemma unit_not_fst:
  shows "Unit \<noteq> Fst P"
proof(transfer)
  fix P :: "'a ptrm"
  show "\<not> PUnit \<approx> PFst P"
  proof(rule classical)
    assume "\<not>\<not> PUnit \<approx> PFst P"
    hence False using unitE by fastforce
    thus ?thesis by blast
  qed
qed

lemma unit_not_snd:
  shows "Unit \<noteq> Snd P"
proof(transfer)
  fix P :: "'a ptrm"
  show "\<not> PUnit \<approx> PSnd P"
  proof(rule classical)
    assume "\<not>\<not> PUnit \<approx> PSnd P"
    hence False using unitE by fastforce
    thus ?thesis by blast
  qed
qed

lemma var_not_app:
  shows "Var x \<noteq> App A B"
proof(transfer)
  fix x :: 'a and A B
  show "\<not>PVar x \<approx> PApp A B"
  proof(rule classical)
    assume "\<not>\<not>PVar x \<approx> PApp A B"
    hence False using varE by fastforce
    thus ?thesis by blast
  qed
qed

lemma var_not_fn:
  shows "Var x \<noteq> Fn y T A"
proof(transfer)
  fix x y :: 'a and T A
  show "\<not>PVar x \<approx> PFn y T A"
  proof(rule classical)
    assume "\<not>\<not>PVar x \<approx> PFn y T A" 
    hence False using varE by fastforce
    thus ?thesis by blast
  qed
qed

lemma var_not_pair:
  shows "Var x \<noteq> Pair A B"
proof(transfer)
  fix x :: 'a and A B
  show "\<not>PVar x \<approx> PPair A B"
  proof(rule classical)
    assume "\<not>\<not>PVar x \<approx> PPair A B"
    hence False using varE by fastforce
    thus ?thesis by blast
  qed
qed

lemma var_not_fst:
  shows "Var x \<noteq> Fst P"
proof(transfer)
  fix x :: 'a and P
  show "\<not>PVar x \<approx> PFst P"
  proof(rule classical)
    assume "\<not>\<not>PVar x \<approx> PFst P"
    hence False using varE by fastforce
    thus ?thesis by blast
  qed
qed

lemma var_not_snd:
  shows "Var x \<noteq> Snd P"
proof(transfer)
  fix x :: 'a and P
  show "\<not>PVar x \<approx> PSnd P"
  proof(rule classical)
    assume "\<not>\<not>PVar x \<approx> PSnd P"
    hence False using varE by fastforce
    thus ?thesis by blast
  qed
qed

lemma app_not_fn:
  shows "App A B \<noteq> Fn y T X"
proof(transfer)
  fix y :: 'a and A B T X
  show "\<not>PApp A B \<approx> PFn y T X"
  proof(rule classical)
    assume "\<not>\<not>PApp A B \<approx> PFn y T X"
    hence False using appE by auto
    thus ?thesis by blast
  qed
qed

lemma app_not_pair:
  shows "App A B \<noteq> Pair C D"
proof(transfer)
  fix A B C D :: "'a ptrm"
  show "\<not>PApp A B \<approx> PPair C D"
  proof(rule classical)
    assume "\<not>\<not>PApp A B \<approx> PPair C D"
    hence False using appE by auto
    thus ?thesis by blast
  qed
qed

lemma app_not_fst:
  shows "App A B \<noteq> Fst P"
proof(transfer)
  fix A B P :: "'a ptrm"
  show "\<not>PApp A B \<approx> PFst P"
  proof(rule classical)
    assume "\<not>\<not>PApp A B \<approx> PFst P"
    hence False using appE by auto
    thus ?thesis by blast
  qed
qed

lemma app_not_snd:
  shows "App A B \<noteq> Snd P"
proof(transfer)
  fix A B P :: "'a ptrm"
  show "\<not>PApp A B \<approx> PSnd P"
  proof(rule classical)
    assume "\<not>\<not>PApp A B \<approx> PSnd P"
    hence False using appE by auto
    thus ?thesis by blast
  qed
qed

lemma fn_not_pair:
  shows "Fn x T A \<noteq> Pair C D"
proof(transfer)
  fix x :: 'a and T A C D
  show "\<not>PFn x T A \<approx> PPair C D"
  proof(rule classical)
    assume "\<not>\<not>PFn x T A \<approx> PPair C D"
    hence False using fnE by fastforce
    thus ?thesis by blast
  qed
qed

lemma fn_not_fst:
  shows "Fn x T A \<noteq> Fst P"
proof(transfer)
  fix x :: 'a and T A P
  show "\<not>PFn x T A \<approx> PFst P"
  proof(rule classical)
    assume "\<not>\<not>PFn x T A \<approx> PFst P"
    hence False using fnE by fastforce
    thus ?thesis by blast
  qed
qed

lemma fn_not_snd:
  shows "Fn x T A \<noteq> Snd P"
proof(transfer)
  fix x :: 'a and T A P
  show "\<not>PFn x T A \<approx> PSnd P"
  proof(rule classical)
    assume "\<not>\<not>PFn x T A \<approx> PSnd P"
    hence False using fnE by fastforce
    thus ?thesis by blast
  qed
qed

lemma pair_not_fst:
  shows "Pair A B \<noteq> Fst P"
proof(transfer)
  fix A B P :: "'a ptrm"
  show "\<not>PPair A B \<approx> PFst P"
  proof(rule classical)
    assume "\<not>\<not>PPair A B \<approx> PFst P"
    hence False using pairE by auto
    thus ?thesis by blast
  qed
qed

lemma pair_not_snd:
  shows "Pair A B \<noteq> Snd P"
proof(transfer)
  fix A B P :: "'a ptrm"
  show "\<not>PPair A B \<approx> PSnd P"
  proof(rule classical)
    assume "\<not>\<not>PPair A B \<approx> PSnd P"
    hence False using pairE by auto
    thus ?thesis by blast
  qed
qed

lemma fst_not_snd:
  shows "Fst P \<noteq> Snd Q"
proof(transfer)
  fix P Q :: "'a ptrm"
  show "\<not>PFst P \<approx> PSnd Q"
  proof(rule classical)
    assume "\<not>\<not>PFst P \<approx> PSnd Q"
    hence False using fstE by auto
    thus ?thesis by blast
  qed
qed

lemma trm_simp:
  shows
    "Var x = Var y \<Longrightarrow> x = y"
    "App A B = App C D \<Longrightarrow> A = C"
    "App A B = App C D \<Longrightarrow> B = D"
    "Fn x T A = Fn y S B \<Longrightarrow>
      (x = y \<and> T = S \<and> A = B) \<or> (x \<noteq> y \<and> T = S \<and> x \<notin> fvs B \<and> A = [x \<leftrightarrow> y] \<cdot> B)"
    "Pair A B = Pair C D \<Longrightarrow> A = C"
    "Pair A B = Pair C D \<Longrightarrow> B = D"
    "Fst P = Fst Q \<Longrightarrow> P = Q"
    "Snd P = Snd Q \<Longrightarrow> P = Q"
  apply (transfer, insert ptrm.inject varE, fastforce)[]
  apply (transfer, insert ptrm.inject appE, auto)[]
  apply (transfer, insert ptrm.inject appE, auto)[]
  defer
  apply (transfer, insert pairE ptrm.inject, auto)[]
  apply (transfer, insert pairE ptrm.inject, auto)[]
  apply (transfer, insert fstE ptrm.inject, auto)[]
  apply (transfer, insert sndE ptrm.inject, auto)[]
proof(transfer')
  fix x y :: 'a and T S :: type and A B :: "'a ptrm"
  assume *: "PFn x T A \<approx> PFn y S B"
  thus "x = y \<and> T = S \<and> A \<approx> B \<or> x \<noteq> y \<and> T = S \<and> x \<notin> ptrm_fvs B \<and> A \<approx> [x \<leftrightarrow> y] \<bullet> B"
  proof(induction rule: fnE[where x=x and T=T and A=A and Y="PFn y S B"], metis *)
    case (2 C)
      thus ?case by simp
    next
    case (3 z C)
      thus ?case by simp
    next
  qed
qed

lemma fn_eq:
  assumes "x \<noteq> y" "x \<notin> fvs B" "A = [x \<leftrightarrow> y] \<cdot> B"
  shows "Fn x T A = Fn y T B"
using assms by(transfer', metis ptrm_alpha_equiv.fn2)

lemma trm_prm_simp:
  shows
    "\<pi> \<cdot> Unit = Unit"
    "\<pi> \<cdot> Var x = Var (\<pi> $ x)"
    "\<pi> \<cdot> App A B = App (\<pi> \<cdot> A) (\<pi> \<cdot> B)"
    "\<pi> \<cdot> Fn x T A = Fn (\<pi> $ x) T (\<pi> \<cdot> A)"
    "\<pi> \<cdot> Pair A B = Pair (\<pi> \<cdot> A) (\<pi> \<cdot> B)"
    "\<pi> \<cdot> Fst P = Fst (\<pi> \<cdot> P)"
    "\<pi> \<cdot> Snd P = Snd (\<pi> \<cdot> P)"
  apply (transfer, auto simp add: ptrm_alpha_equiv_reflexive)
  apply (transfer', auto simp add: ptrm_alpha_equiv_reflexive)
  apply ((transfer, auto simp add: ptrm_alpha_equiv_reflexive)+)
done

lemma trm_prm_apply_compose:
  shows "\<pi> \<cdot> \<sigma> \<cdot> A = (\<pi> \<diamondop> \<sigma>) \<cdot> A"
by(transfer', metis ptrm_prm_apply_compose ptrm_alpha_equiv_reflexive)

lemma fvs_finite:
  shows "finite (fvs M)"
by(transfer, metis ptrm_fvs_finite)

lemma fvs_simp:
  shows
    "fvs Unit = {}" and
    "fvs (Var x) = {x}"
    "fvs (App A B) = fvs A \<union> fvs B"
    "fvs (Fn x T A) = fvs A - {x}"
    "fvs (Pair A B) = fvs A \<union> fvs B"
    "fvs (Fst P) = fvs P"
    "fvs (Snd P) = fvs P"
by((transfer, simp)+)

lemma var_prm_action:
  shows "[a \<leftrightarrow> b] \<cdot> Var a = Var b"
by(transfer', simp add: prm_unit_action ptrm_alpha_equiv.intros)

lemma var_prm_inaction:
  assumes "a \<noteq> x" "b \<noteq> x"
  shows "[a \<leftrightarrow> b] \<cdot> Var x = Var x"
using assms by(transfer', simp add: prm_unit_inaction ptrm_alpha_equiv.intros)

lemma trm_prm_apply_id:
  shows "\<epsilon> \<cdot> M = M"
by(transfer', auto simp add: ptrm_prm_apply_id)

lemma trm_prm_unit_inaction:
  assumes "a \<notin> fvs X" "b \<notin> fvs X"
  shows "[a \<leftrightarrow> b] \<cdot> X = X"
using assms by(transfer', metis ptrm_prm_unit_inaction)
 
lemma trm_prm_agreement_equiv:
  assumes "\<And>a. a \<in> ds \<pi> \<sigma> \<Longrightarrow> a \<notin> fvs M"
  shows "\<pi> \<cdot> M = \<sigma> \<cdot> M"
using assms by(transfer, metis ptrm_prm_agreement_equiv)

lemma trm_induct:
  fixes P :: "'a trm \<Rightarrow> bool"
  assumes
    "P Unit"
    "\<And>x. P (Var x)"
    "\<And>A B. \<lbrakk>P A; P B\<rbrakk> \<Longrightarrow> P (App A B)"
    "\<And>x T A. P A \<Longrightarrow> P (Fn x T A)"
    "\<And>A B. \<lbrakk>P A; P B\<rbrakk> \<Longrightarrow> P (Pair A B)"
    "\<And>A. P A \<Longrightarrow> P (Fst A)"
    "\<And>A. P A \<Longrightarrow> P (Snd A)"
  shows "P M"
proof -
  have "\<And>X. P (abs_trm X)"
  proof(rule ptrm.induct)
    show "P (abs_trm PUnit)"
      using assms(1) Unit.abs_eq by metis
    show "P (abs_trm (PVar x))" for x
      using assms(2) Var.abs_eq by metis
    show "\<lbrakk>P (abs_trm A); P (abs_trm B)\<rbrakk> \<Longrightarrow> P (abs_trm (PApp A B))" for A B
      using assms(3) App.abs_eq by metis
    show "P (abs_trm A) \<Longrightarrow> P (abs_trm (PFn x T A))" for x T A
      using assms(4) Fn.abs_eq by metis
    show "\<lbrakk>P (abs_trm A); P (abs_trm B)\<rbrakk> \<Longrightarrow> P (abs_trm (PPair A B))" for A B
      using assms(5) Pair.abs_eq by metis
    show "P (abs_trm A) \<Longrightarrow> P (abs_trm (PFst A))" for A
      using assms(6) Fst.abs_eq by metis
    show "P (abs_trm A) \<Longrightarrow> P (abs_trm (PSnd A))" for A
      using assms(7) Snd.abs_eq by metis
  qed
  thus ?thesis using trm.abs_induct by auto
qed

lemma trm_cases:
  assumes
    "M = Unit \<Longrightarrow> P M"
    "\<And>x. M = Var x \<Longrightarrow> P M"
    "\<And>A B. M = App A B \<Longrightarrow> P M"
    "\<And>x T A. M = Fn x T A \<Longrightarrow> P M"
    "\<And>A B. M = Pair A B \<Longrightarrow> P M"
    "\<And>A. M = Fst A \<Longrightarrow> P M"
    "\<And>A. M = Snd A \<Longrightarrow> P M"
  shows "P M"
using assms by(induction rule: trm_induct, auto)

lemma trm_depth_induct:
  assumes
    "P Unit"
    "\<And>x. P (Var x)"
    "\<And>A B. \<lbrakk>\<And>K. depth K < depth (App A B) \<Longrightarrow> P K\<rbrakk> \<Longrightarrow> P (App A B)"
    "\<And>M x T A. (\<And>K. depth K < depth (Fn x T A) \<Longrightarrow> P K) \<Longrightarrow> P (Fn x T A)"
    "\<And>A B. \<lbrakk>\<And>K. depth K < depth (Pair A B) \<Longrightarrow> P K\<rbrakk> \<Longrightarrow> P (Pair A B)"
    "\<And>A. \<lbrakk>\<And>K. depth K < depth (Fst A) \<Longrightarrow> P K\<rbrakk> \<Longrightarrow> P (Fst A)"
    "\<And>A. \<lbrakk>\<And>K. depth K < depth (Snd A) \<Longrightarrow> P K\<rbrakk> \<Longrightarrow> P (Snd A)"
  shows "P M"
proof(induction "depth M" arbitrary: M rule: less_induct)
  fix M :: "'a trm"
  assume IH: "depth K < depth M \<Longrightarrow> P K" for K
  hence
    "         M = Unit \<Longrightarrow>    P M"
    "\<And>x.     M = Var x \<Longrightarrow>    P M"
    "\<And>A B.   M = App A B \<Longrightarrow>  P M"
    "\<And>x T A. M = Fn x T A \<Longrightarrow> P M"
    "\<And>A B.   M = Pair A B \<Longrightarrow>  P M"
    "\<And>A.     M = Fst A \<Longrightarrow>  P M"
    "\<And>A.     M = Snd A \<Longrightarrow>  P M"
    using assms by blast+
  thus "P M" using trm_cases[where M=M] by blast
qed

context fresh begin

lemma fresh_fn:
  fixes x :: 'a
  shows "\<exists>y B. x \<noteq> y \<and> y \<notin> fvs M \<and> (Fn x T A = Fn y T B)"
proof -
  have *: "finite ({x} \<union> fvs A \<union> fvs M)" using fvs_finite by auto
  obtain y where "y = fresh_in ({x} \<union> fvs A \<union> fvs M)" by auto
  hence "y \<notin> ({x} \<union> fvs A \<union> fvs M)" using fresh_axioms * unfolding class.fresh_def by metis
  hence "y \<noteq> x" "y \<notin> fvs A" "y \<notin> fvs M" by auto

  obtain B where "B = [y \<leftrightarrow> x] \<cdot> A" by auto
  hence "Fn x T A = Fn y T B" using fn_eq `y \<noteq> x` `y \<notin> fvs A` by metis
  thus ?thesis using `y \<noteq> x` `y \<notin> fvs M` by metis
qed

lemma trm_strong_induct:
  fixes P :: "'a set \<Rightarrow> 'a trm \<Rightarrow> bool"
  assumes
    "P S Unit"
    "\<And>x. P S (Var x)"
    "\<And>A B. \<lbrakk>P S A; P S B\<rbrakk> \<Longrightarrow> P S (App A B)"
    "\<And>x T. x \<notin> S \<Longrightarrow> (\<And>A. P S A \<Longrightarrow> P S (Fn x T A))"
    "\<And>A B. \<lbrakk>P S A; P S B\<rbrakk> \<Longrightarrow> P S (Pair A B)"
    "\<And>A. P S A \<Longrightarrow> P S (Fst A)"
    "\<And>A. P S A \<Longrightarrow> P S (Snd A)"
    "finite S"
  shows "P S M"
proof -
  have "\<And>\<pi>. P S (\<pi> \<cdot> M)"
  proof(induction M rule: trm_induct)
    case 1
      thus ?case using assms(1) trm_prm_simp(1) by metis
    next
    case (2 x)
      thus ?case using assms(2) trm_prm_simp(2) by metis
    next
    case (3 A B)
      thus ?case using assms(3) trm_prm_simp(3) by metis
    next
    case (4 x T A)
      have "finite S" "finite (fvs (\<pi> \<cdot> A))" "finite {\<pi> $ x}"
        using `finite S` fvs_finite by auto
      hence "finite (S \<union> fvs (\<pi> \<cdot> A) \<union> {\<pi> $ x})" by auto
      
      obtain y where "y = fresh_in (S \<union> fvs (\<pi> \<cdot> A) \<union> {\<pi> $ x})" by auto
      hence "y \<notin> S \<union> fvs (\<pi> \<cdot> A) \<union> {\<pi> $ x}" using fresh_axioms unfolding class.fresh_def
        using `finite (S \<union> fvs (\<pi> \<cdot> A) \<union> {\<pi> $ x})` by metis
      hence "y \<noteq> \<pi> $ x" "y \<notin> fvs (\<pi> \<cdot> A)" "y \<notin> S" by auto
      hence *: "\<And>A. P S A \<Longrightarrow> P S (Fn y T A)" using assms(4) by metis
  
      have "P S (([y \<leftrightarrow> \<pi> $ x] \<diamondop> \<pi>) \<cdot> A)" using 4 by metis
      moreover hence "P S (Fn y T (([y \<leftrightarrow> \<pi> $ x] \<diamondop> \<pi>) \<cdot> A))" using * by metis
      moreover have "(Fn y T (([y \<leftrightarrow> \<pi> $ x] \<diamondop> \<pi>) \<cdot> A)) = Fn (\<pi> $ x) T (\<pi> \<cdot> A)"
        using trm_prm_apply_compose fn_eq `y \<noteq> \<pi> $ x` `y \<notin> fvs (\<pi> \<cdot> A)` by metis
      ultimately show ?case using trm_prm_simp(4) by metis
    next
    case (5 A B)
      thus ?case using assms(5) trm_prm_simp(5) by metis
    next
    case (6 A)
      thus ?case using assms(6) trm_prm_simp(6) by metis
    next
    case (7 A)
      thus ?case using assms(7) trm_prm_simp(7) by metis
    next
  qed
  hence "P S (\<epsilon> \<cdot> M)" by metis
  thus "P S M" using trm_prm_apply_id by metis
qed

lemma trm_strong_cases:
  fixes P :: "'a set \<Rightarrow> 'a trm \<Rightarrow> bool"
  assumes
    "         M = Unit    \<Longrightarrow> P S M"
    "\<And>x.     M = Var x    \<Longrightarrow> P S M"
    "\<And>A B.   M = App A B  \<Longrightarrow> P S M"
    "\<And>x T A. M = Fn x T A \<Longrightarrow> x \<notin> S \<Longrightarrow> P S M"
    "\<And>A B.   M = Pair A B \<Longrightarrow> P S M"
    "\<And>A.     M = Fst A    \<Longrightarrow> P S M"
    "\<And>A.     M = Snd A    \<Longrightarrow> P S M"
    "finite S"
  shows "P S M"
using assms by(induction S M rule: trm_strong_induct, metis+)

lemma trm_strong_depth_induct:
  fixes P :: "'a set \<Rightarrow> 'a trm \<Rightarrow> bool"
  assumes
    "P S Unit"
    "\<And>x. P S (Var x)"
    "\<And>A B. \<lbrakk>\<And>K. depth K < depth (App A B) \<Longrightarrow> P S K\<rbrakk> \<Longrightarrow> P S (App A B)"
    "\<And>x T. x \<notin> S \<Longrightarrow> (\<And>A. (\<And>K. depth K < depth (Fn x T A) \<Longrightarrow> P S K) \<Longrightarrow> P S (Fn x T A))"
    "\<And>A B. \<lbrakk>\<And>K. depth K < depth (Pair A B) \<Longrightarrow> P S K\<rbrakk> \<Longrightarrow> P S (Pair A B)"
    "\<And>A. \<lbrakk>\<And>K. depth K < depth (Fst A) \<Longrightarrow> P S K\<rbrakk> \<Longrightarrow> P S (Fst A)"
    "\<And>A. \<lbrakk>\<And>K. depth K < depth (Snd A) \<Longrightarrow> P S K\<rbrakk> \<Longrightarrow> P S (Snd A)"
    "finite S"
  shows "P S M"
proof(induction "depth M" arbitrary: M rule: less_induct)
  fix M :: "'a trm"
  assume IH: "depth K < depth M \<Longrightarrow> P S K" for K
  hence
    "         M = Unit    \<Longrightarrow> P S M"
    "\<And>x.     M = Var x    \<Longrightarrow> P S M"
    "\<And>A B.   M = App A B  \<Longrightarrow> P S M"
    "\<And>x T A. M = Fn x T A \<Longrightarrow> x \<notin> S \<Longrightarrow> P S M"
    "\<And>A B.   M = Pair A B \<Longrightarrow> P S M"
    "\<And>A.     M = Fst A    \<Longrightarrow> P S M"
    "\<And>A.     M = Snd A    \<Longrightarrow> P S M"
    "finite S"
    using assms IH by metis+
  thus "P S M" using trm_strong_cases[where M=M] by blast
qed

lemma trm_prm_fvs:
  shows "fvs (\<pi> \<cdot> M) = \<pi> {$} fvs M"
by(transfer, metis ptrm_prm_fvs)

inductive typing :: "'a typing_ctx \<Rightarrow> 'a trm \<Rightarrow> type \<Rightarrow> bool" ("_ \<turnstile> _ : _") where
  tunit: "\<Gamma> \<turnstile> Unit : TUnit"
| tvar:  "\<Gamma> x = Some \<tau> \<Longrightarrow> \<Gamma> \<turnstile> Var x : \<tau>"
| tapp:  "\<lbrakk>\<Gamma> \<turnstile> f : (TArr \<tau> \<sigma>); \<Gamma> \<turnstile> x : \<tau>\<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> App f x : \<sigma>"
| tfn:   "\<Gamma>(x \<mapsto> \<tau>) \<turnstile> A : \<sigma> \<Longrightarrow> \<Gamma> \<turnstile> Fn x \<tau> A : (TArr \<tau> \<sigma>)"
| tpair: "\<lbrakk>\<Gamma> \<turnstile> A : \<tau>; \<Gamma> \<turnstile> B : \<sigma>\<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> Pair A B : (TPair \<tau> \<sigma>)"
| tfst:  "\<Gamma> \<turnstile> P : (TPair \<tau> \<sigma>) \<Longrightarrow> \<Gamma> \<turnstile> Fst P : \<tau>"
| tsnd:  "\<Gamma> \<turnstile> P : (TPair \<tau> \<sigma>) \<Longrightarrow> \<Gamma> \<turnstile> Snd P : \<sigma>"

lemma typing_prm:
  assumes "\<Gamma> \<turnstile> M : \<tau>" "\<And>y. y \<in> fvs M \<Longrightarrow> \<Gamma> y = \<Delta> (\<pi> $ y)"
  shows "\<Delta> \<turnstile> \<pi> \<cdot> M : \<tau>"
using assms proof(induction arbitrary: \<Delta> rule: typing.induct)
  case (tunit \<Gamma>)
    thus ?case using typing.tunit trm_prm_simp(1) by metis
  next
  case (tvar \<Gamma> x \<tau>)
    thus ?case using typing.tvar trm_prm_simp(2) fvs_simp(2) singletonI by metis
  next
  case (tapp \<Gamma> A \<tau> \<sigma> B)
    thus ?case using typing.tapp trm_prm_simp(3) fvs_simp(3) UnCI by metis
  next
  case (tfn \<Gamma> x \<tau> A \<sigma>)
    have "y \<in> fvs A \<Longrightarrow> (\<Gamma>(x \<mapsto> \<tau>)) y = (\<Delta>(\<pi> $ x \<mapsto> \<tau>)) (\<pi> $ y)" for y
    proof(cases "y = x")
      case True
        thus ?thesis using fun_upd_apply by simp
      next
      case False
        assume "y \<in> fvs A"
        hence "y \<in> fvs (Fn x \<tau> A)" using fvs_simp(4) `y \<noteq> x` DiffI singletonD by fastforce
        hence "\<Gamma> y = \<Delta> (\<pi> $ y)" using tfn.prems by metis
        thus ?thesis by (simp add: prm_apply_unequal)
      next
    qed
    hence "\<Delta>(\<pi> $ x \<mapsto> \<tau>) \<turnstile> \<pi> \<cdot> A : \<sigma>" using tfn.IH by metis
    thus ?case using trm_prm_simp(4) typing.tfn by metis
  next
  case (tpair \<Gamma> A B)
    thus ?case using typing.tpair trm_prm_simp(5) fvs_simp(5) UnCI by metis
  next
  case (tfst \<Gamma> P \<tau> \<sigma>)
    thus ?case using typing.tfst trm_prm_simp(6) fvs_simp(6) by metis
  next
  case (tsnd \<Gamma> P \<tau> \<sigma>)
    thus ?case using typing.tsnd trm_prm_simp(7) fvs_simp(7) by metis
  next
qed

lemma typing_swp:
  assumes "\<Gamma>(a \<mapsto> \<sigma>) \<turnstile> M : \<tau>" "b \<notin> fvs M"
  shows "\<Gamma>(b \<mapsto> \<sigma>) \<turnstile> [a \<leftrightarrow> b] \<cdot> M : \<tau>"
proof -
  (* hack to make induction work sensibly *)
  obtain \<Delta> where \<Delta>: "\<Delta> = \<Gamma>(a \<mapsto> \<sigma>)" by auto
  hence "\<Delta> \<turnstile> M : \<tau>" using assms by auto
  thus ?thesis using \<Delta> `b \<notin> fvs M`
  proof(induction arbitrary: \<Gamma> \<sigma> a b rule: typing.induct)
    case (tunit \<Delta>)
      thus ?case using typing.tunit trm_prm_simp(1) by metis
    next
    case (tvar \<Delta> x \<tau>)
      have "fvs (Var x) = {x}" using fvs_simp by fastforce
      hence "x \<noteq> b" using tvar.prems by auto
      consider "x = a" | "x \<noteq> a" by auto
      thus ?case proof(cases)
        case 1
          hence "\<tau> = \<sigma>" using tvar by simp
          thus ?thesis using `x = a` typing.tvar var_prm_action fun_upd_same by metis
        next
        case 2
          thus ?thesis
            using tvar var_prm_inaction `x \<noteq> b` typing.tvar map_upd_Some_unfold
            by (metis (no_types, lifting))
        next
      qed
    next
    case (tapp \<Delta> A \<tau>' \<tau> B)
      have "b \<notin> fvs A" and "b \<notin> fvs B"
        using `b \<notin> fvs (App A B)` fvs_simp(3) UnCI by metis+
      hence "\<Gamma>(b \<mapsto> \<sigma>) \<turnstile> [a \<leftrightarrow> b] \<cdot> A : (TArr \<tau>' \<tau>)" and "\<Gamma>(b \<mapsto> \<sigma>) \<turnstile> [a \<leftrightarrow> b] \<cdot> B : \<tau>'"
        using tapp.IH tapp.prems by metis+
      hence "\<Gamma>(b \<mapsto> \<sigma>) \<turnstile> App ([a \<leftrightarrow> b] \<cdot> A) ([a \<leftrightarrow> b] \<cdot> B) : \<tau>"
        using typing.tapp by metis
      thus ?case using trm_prm_simp(3) by metis
    next
    case (tfn \<Delta> x T A \<tau>)
      from this consider "b = x" | "b \<noteq> x \<and> b \<notin> fvs A" using fvs_simp(4)
        using DiffI singletonD by fastforce
      thus ?case proof(cases)
        case 1
          have "\<Gamma>(a \<mapsto> \<sigma>) \<turnstile> Fn x T A : (TArr T \<tau>)" using tfn.hyps tfn.prems(1) typing.tfn by metis
          moreover have "y \<in> fvs (Fn x T A) \<Longrightarrow> (\<Gamma>(a \<mapsto> \<sigma>)) y = (\<Gamma>(b \<mapsto> \<sigma>)) ([a \<leftrightarrow> b] $ y)" for y
            using prm_unit_action prm_unit_inaction tfn.prems(2) by fastforce
          ultimately show ?thesis using typing_prm[where
            \<Gamma>="\<Gamma>(a \<mapsto> \<sigma>)" and
            M="Fn x T A" and
            \<tau>="TArr T \<tau>" and
            \<pi>="[a \<leftrightarrow> b]" and
            \<Delta>="\<Gamma>(b \<mapsto> \<sigma>)"
          ] by metis
        next
        case 2
          hence "b \<noteq> x" and "b \<notin> fvs A" by auto
          consider "a = x" | "a \<noteq> x" by auto
          thus ?thesis proof(cases)
            case 1
              hence *: "[a \<leftrightarrow> b] \<cdot> Fn x T A = Fn b T ([a \<leftrightarrow> b] \<cdot> A)"
                using trm_prm_simp(4) prm_unit_action by metis
              have "\<Delta>(x \<mapsto> T) = \<Gamma>(a \<mapsto> T)" using `a = x` tfn.prems(1) by auto
              hence "\<Gamma>(b \<mapsto> T) \<turnstile> [a \<leftrightarrow> b] \<cdot> A : \<tau>" using tfn.IH `b \<notin> fvs A` by metis
              thus ?thesis using typing.tfn * fun_upd_upd by metis
            next
            case 2
              hence *: "[a \<leftrightarrow> b] \<cdot> Fn x T A = Fn x T ([a \<leftrightarrow> b] \<cdot> A)"
                using trm_prm_simp(4) prm_unit_inaction `b \<noteq> x` by metis
              have "\<Delta>(x \<mapsto> T) = \<Gamma>(x \<mapsto> T)(a \<mapsto> \<sigma>)" using tfn.prems(1) `a \<noteq> x` by auto
              hence "\<Gamma>(x \<mapsto> T)(b \<mapsto> \<sigma>) \<turnstile> [a \<leftrightarrow> b] \<cdot> A : \<tau>" using tfn.IH `b \<notin> fvs A` by metis
              hence "\<Gamma>(b \<mapsto> \<sigma>)(x \<mapsto> T) \<turnstile> [a \<leftrightarrow> b] \<cdot> A : \<tau>" using `b \<noteq> x`
                by (simp add: fun_upd_twist)
              thus ?thesis using typing.tfn * by metis
            next
          qed
        next
      qed
    next
    case (tpair \<Delta> A \<tau>' B \<sigma>)
      thus ?case using typing.tpair by (simp add: fvs_simp trm_prm_simp)
    next
    case (tfst \<Delta> P \<tau> \<sigma>)
      thus ?case using typing.tfst fvs_simp(6) trm_prm_simp(6) by (metis (full_types))
    next
    case (tsnd \<Delta> P \<tau> \<sigma>)
      thus ?case using typing.tsnd fvs_simp(7) trm_prm_simp(7) by (metis (full_types))
    next
  qed
qed

lemma typing_unitE:
  assumes "\<Gamma> \<turnstile> Unit : \<tau>"
  shows "\<tau> = TUnit"
using assms
  apply cases
  apply blast
  apply (auto simp add: unit_not_var unit_not_app unit_not_fn unit_not_pair unit_not_fst unit_not_snd)
done

lemma typing_varE:
  assumes "\<Gamma> \<turnstile> Var x : \<tau>"
  shows "\<Gamma> x = Some \<tau>"
using assms
  apply cases
  prefer 2
  apply (metis trm_simp(1))
  apply (metis unit_not_var)
  apply (auto simp add: var_not_app var_not_fn var_not_pair var_not_fst var_not_snd)
done

lemma typing_appE:
  assumes "\<Gamma> \<turnstile> App A B : \<sigma>"
  shows "\<exists>\<tau>. (\<Gamma> \<turnstile> A : (TArr \<tau> \<sigma>)) \<and> (\<Gamma> \<turnstile> B : \<tau>)"
using assms
  apply cases
  prefer 3
  apply (metis trm_simp(2, 3))
  apply (metis unit_not_app)
  apply (metis var_not_app)
  apply (auto simp add: app_not_fn app_not_pair app_not_fst app_not_snd)
done

lemma typing_fnE:
  assumes "\<Gamma> \<turnstile> Fn x T A : \<theta>"
  shows "\<exists>\<sigma>. \<theta> = (TArr T \<sigma>) \<and> (\<Gamma>(x \<mapsto> T) \<turnstile> A : \<sigma>)"
using assms
  apply cases
  apply (metis unit_not_fn)
  apply (metis var_not_fn)
  apply (metis app_not_fn)
  defer
  apply (metis fn_not_pair, metis fn_not_fst, metis fn_not_snd)
proof -
  case (tfn y S B \<sigma>)
    from this consider
      "x = y \<and> T = S \<and> A = B" | "x \<noteq> y \<and> T = S \<and> x \<notin> fvs B \<and> A = [x \<leftrightarrow> y] \<cdot> B"
      using trm_simp(4) by metis
    thus ?thesis proof(cases)
      case 1
        thus ?thesis using tfn by metis
      next
      case 2
        thus ?thesis using tfn typing_swp prm_unit_commutes by metis
      next
    qed
  next
qed

lemma typing_pairE:
  assumes "\<Gamma> \<turnstile> Pair A B : \<theta>"
  shows "\<exists>\<tau> \<sigma>. \<theta> = (TPair \<tau> \<sigma>) \<and> (\<Gamma> \<turnstile> A : \<tau>) \<and> (\<Gamma> \<turnstile> B : \<sigma>)"
using assms
  apply cases
  apply (metis unit_not_pair, metis var_not_pair, metis app_not_pair, metis fn_not_pair)
  defer
  apply (metis pair_not_fst, metis pair_not_snd)
proof -
  case (tpair A \<tau> B \<sigma>)
    thus ?thesis using trm_simp(5) trm_simp(6) by blast
  next
qed

lemma typing_fstE:
  assumes "\<Gamma> \<turnstile> Fst P : \<tau>"
  shows "\<exists>\<sigma>. (\<Gamma> \<turnstile> P : (TPair \<tau> \<sigma>))"
using assms
  apply cases
  apply (metis unit_not_fst, metis var_not_fst, metis app_not_fst, metis fn_not_fst, metis pair_not_fst)
  defer
  apply (metis fst_not_snd)
proof -
  case (tfst P \<sigma>)
    thus ?thesis using trm_simp(7) by blast
  next
qed

lemma typing_sndE:
  assumes "\<Gamma> \<turnstile> Snd P : \<sigma>"
  shows "\<exists>\<tau>. (\<Gamma> \<turnstile> P : (TPair \<tau> \<sigma>))"
using assms
  apply cases
  apply (metis unit_not_snd, metis var_not_snd, metis app_not_snd, metis fn_not_snd, metis pair_not_snd, metis fst_not_snd)
proof -
  case (tsnd P \<sigma>)
    thus ?thesis using trm_simp(8) by blast
  next
qed

theorem typing_weaken:
  assumes "\<Gamma> \<turnstile> M : \<tau>" "y \<notin> fvs M"
  shows "\<Gamma>(y \<mapsto> \<sigma>) \<turnstile> M : \<tau>"
using assms proof(induction rule: typing.induct)
  case (tunit \<Gamma>)
    thus ?case using typing.tunit by metis
  next
  case (tvar \<Gamma> x \<tau>)
    hence "y \<noteq> x" using fvs_simp(2) singletonI by force
    hence "(\<Gamma>(y \<mapsto> \<sigma>)) x = Some \<tau>" using tvar.hyps fun_upd_apply by simp
    thus ?case using typing.tvar by metis
  next
  case (tapp \<Gamma> f \<tau> \<tau>' x)
    from `y \<notin> fvs (App f x)` have "y \<notin> fvs f" "y \<notin> fvs x" using fvs_simp(3) Un_iff by force+
    hence "\<Gamma>(y \<mapsto> \<sigma>) \<turnstile> f : (TArr \<tau> \<tau>')" "\<Gamma>(y \<mapsto> \<sigma>) \<turnstile> x : \<tau>" using tapp.IH by metis+
    thus ?case using typing.tapp by metis
  next
  case (tfn \<Gamma> x \<tau> A \<tau>')
    from `y \<notin> fvs (Fn x \<tau> A)` consider "y = x" | "y \<noteq> x \<and> y \<notin> fvs A"
      using fvs_simp(4) DiffI empty_iff insert_iff by fastforce
    thus ?case proof(cases)
      case 1
        hence "(\<Gamma>(y \<mapsto> \<sigma>)(x \<mapsto> \<tau>)) \<turnstile> A : \<tau>'" using tfn.hyps fun_upd_upd by simp
        thus ?thesis using typing.tfn by metis
      next
      case 2
        hence "y \<noteq> x" "y \<notin> fvs A" by auto
        hence "\<Gamma>(x \<mapsto> \<tau>, y \<mapsto> \<sigma>) \<turnstile> A : \<tau>'" using tfn.IH by metis
        hence "\<Gamma>(y \<mapsto> \<sigma>, x \<mapsto> \<tau>) \<turnstile> A : \<tau>'" using `y \<noteq> x` fun_upd_twist by metis
        thus ?thesis using typing.tfn by metis
      next
    qed
  next
  case (tpair \<Gamma> A \<tau> B \<sigma>)
    thus ?case using typing.tpair fvs_simp(5) UnCI by metis
  next
  case (tfst \<Gamma> P \<tau> \<sigma>)
    thus ?case using typing.tfst fvs_simp(6) by metis
  next
  case (tsnd \<Gamma> P \<tau> \<sigma>)
    thus ?case using typing.tsnd fvs_simp(7) by metis
  next
qed


lift_definition infer :: "'a typing_ctx \<Rightarrow> 'a trm \<Rightarrow> type option" is ptrm_infer_type
proof(transfer)
  fix \<Gamma> :: "'a typing_ctx" and X Y :: "'a ptrm"
  assume "X \<approx> Y"
  thus "ptrm_infer_type \<Gamma> X = ptrm_infer_type \<Gamma> Y" using ptrm_infer_type_alpha_equiv by auto
qed

export_code infer in SML

lemma infer_simp:
  shows
    "infer \<Gamma> Unit = Some TUnit"
    "infer \<Gamma> (Var x) = \<Gamma> x"
    "infer \<Gamma> (App A B) = (case (infer \<Gamma> A, infer \<Gamma> B) of
       (Some (TArr \<tau> \<sigma>), Some \<tau>') \<Rightarrow> (if \<tau> = \<tau>' then Some \<sigma> else None)
     | _ \<Rightarrow> None
     )"
    "infer \<Gamma> (Fn x \<tau> A) = (case infer (\<Gamma>(x \<mapsto> \<tau>)) A of
       Some \<sigma> \<Rightarrow> Some (TArr \<tau> \<sigma>)
     | None \<Rightarrow> None
    )"
    "infer \<Gamma> (Pair A B) = (case (infer \<Gamma> A, infer \<Gamma> B) of
       (Some \<tau>, Some \<sigma>) \<Rightarrow> Some (TPair \<tau> \<sigma>)
     | _ \<Rightarrow> None
     )"
    "infer \<Gamma> (Fst P) = (case infer \<Gamma> P of
       (Some (TPair \<tau> \<sigma>)) \<Rightarrow> Some \<tau>
     | _ \<Rightarrow> None
     )"
    "infer \<Gamma> (Snd P) = (case infer \<Gamma> P of
       (Some (TPair \<tau> \<sigma>)) \<Rightarrow> Some \<sigma>
     | _ \<Rightarrow> None
     )"
by((transfer, simp)+)

lemma infer_unitE:
  assumes "infer \<Gamma> Unit = Some \<tau>"
  shows "\<tau> = TUnit"
using assms by(transfer, simp)

lemma infer_varE:
  assumes "infer \<Gamma> (Var x) = Some \<tau>"
  shows "\<Gamma> x = Some \<tau>"
using assms by(transfer, simp)

lemma infer_appE:
  assumes "infer \<Gamma> (App A B) = Some \<tau>"
  shows "\<exists>\<sigma>. infer \<Gamma> A = Some (TArr \<sigma> \<tau>) \<and> infer \<Gamma> B = Some \<sigma>"
using assms proof(transfer)
  fix \<Gamma> :: "'a typing_ctx" and A B \<tau>
  assume H: "ptrm_infer_type \<Gamma> (PApp A B) = Some \<tau>"

  have "ptrm_infer_type \<Gamma> A \<noteq> None"
  proof(rule classical, auto)
    assume "ptrm_infer_type \<Gamma> A = None"
    hence "ptrm_infer_type \<Gamma> (PApp A B) = None" by auto
    thus False using H by auto
  qed
  from this obtain T where *: "ptrm_infer_type \<Gamma> A = Some T" by auto

  have "T \<noteq> TVar x" for x
  proof(rule classical, auto)
    fix x
    assume "T = TVar x"
    hence "ptrm_infer_type \<Gamma> A = Some (TVar x)" using * by metis
    hence "ptrm_infer_type \<Gamma> (PApp A B) = None" by simp
    thus False using H by auto
  qed
  moreover have "T \<noteq> TUnit"
  proof(rule classical, auto)
    fix x
    assume "T = TUnit"
    hence "ptrm_infer_type \<Gamma> A = Some TUnit" using * by metis
    hence "ptrm_infer_type \<Gamma> (PApp A B) = None" by simp
    thus False using H by auto
  qed
  moreover have "T \<noteq> TPair \<tau> \<sigma>" for \<tau> \<sigma>
  proof(rule classical, auto)
    fix \<tau> \<sigma>
    assume "T = TPair \<tau> \<sigma>"
    hence "ptrm_infer_type \<Gamma> A = Some (TPair \<tau> \<sigma>)" using * by metis
    hence "ptrm_infer_type \<Gamma> (PApp A B) = None" by simp
    thus False using H by auto
  qed
  ultimately obtain \<sigma> \<tau>' where "T = TArr \<sigma> \<tau>'" by(cases T, blast, auto)
  hence *: "ptrm_infer_type \<Gamma> A = Some (TArr \<sigma> \<tau>')" using * by metis

  have "ptrm_infer_type \<Gamma> B \<noteq> None"
  proof(rule classical, auto)
    assume "ptrm_infer_type \<Gamma> B = None"
    hence "ptrm_infer_type \<Gamma> (PApp A B) = None" using * by auto
    thus False using H by auto
  qed
  from this obtain \<sigma>' where **: "ptrm_infer_type \<Gamma> B = Some \<sigma>'" by auto

  have "\<sigma> = \<sigma>'"
  proof(rule classical)
    assume "\<sigma> \<noteq> \<sigma>'"
    hence "ptrm_infer_type \<Gamma> (PApp A B) = None" using * ** by simp
    hence False using H by auto
    thus "\<sigma> = \<sigma>'" by blast
  qed
  hence **: "ptrm_infer_type \<Gamma> B = Some \<sigma>" using ** by auto

  have "ptrm_infer_type \<Gamma> (PApp A B) = Some \<tau>'" using * ** by auto
  hence "\<tau> = \<tau>'" using H by auto
  hence *: "ptrm_infer_type \<Gamma> A = Some (TArr \<sigma> \<tau>)" using * by auto

  show "\<exists>\<sigma>. ptrm_infer_type \<Gamma> A = Some (TArr \<sigma> \<tau>) \<and> ptrm_infer_type \<Gamma> B = Some \<sigma>"
    using * ** by auto
qed

lemma infer_fnE:
  assumes "infer \<Gamma> (Fn x T A) = Some \<tau>"
  shows "\<exists>\<sigma>. \<tau> = TArr T \<sigma> \<and> infer (\<Gamma>(x \<mapsto> T)) A = Some \<sigma>"
using assms proof(transfer)
  fix x :: 'a and \<Gamma> T A \<tau>
  assume H: "ptrm_infer_type \<Gamma> (PFn x T A) = Some \<tau>"

  have "ptrm_infer_type (\<Gamma>(x \<mapsto> T)) A \<noteq> None"
  proof(rule classical, auto)
    assume "ptrm_infer_type (\<Gamma>(x \<mapsto> T)) A = None"
    hence "ptrm_infer_type \<Gamma> (PFn x T A) = None" by auto
    thus False using H by auto
  qed
  from this obtain \<sigma> where *: "ptrm_infer_type (\<Gamma>(x \<mapsto> T)) A = Some \<sigma>" by auto

  have "ptrm_infer_type \<Gamma> (PFn x T A) = Some (TArr T \<sigma>)" using * by auto
  hence "\<tau> = TArr T \<sigma>" using H by auto
  thus "\<exists>\<sigma>. \<tau> = TArr T \<sigma> \<and> ptrm_infer_type (\<Gamma>(x \<mapsto> T)) A = Some \<sigma>"
    using * by auto
qed

lemma infer_pairE:
  assumes "infer \<Gamma> (Pair A B) = Some \<tau>"
  shows "\<exists>T S. \<tau> = TPair T S \<and> infer \<Gamma> A = Some T \<and> infer \<Gamma> B = Some S"
using assms proof(transfer)
  fix A B :: "'a ptrm" and \<Gamma> \<tau>
  assume H: "ptrm_infer_type \<Gamma> (PPair A B) = Some \<tau>"

  have "ptrm_infer_type \<Gamma> A \<noteq> None"
  proof(rule classical, auto)
    assume "ptrm_infer_type \<Gamma> A = None"
    hence "ptrm_infer_type \<Gamma> (PPair A B) = None" by auto
    thus False using H by auto
  qed
  moreover have "ptrm_infer_type \<Gamma> B \<noteq> None"
  proof(rule classical, auto)
    assume "ptrm_infer_type \<Gamma> B = None"
    hence "ptrm_infer_type \<Gamma> (PPair A B) = None" by (simp add: option.case_eq_if)
    thus False using H by auto
  qed
  ultimately obtain T S
    where "\<tau> = TPair T S" "ptrm_infer_type \<Gamma> A = Some T" "ptrm_infer_type \<Gamma> B = Some S"
    using H by auto
  thus "\<exists>T S. \<tau> = TPair T S \<and> ptrm_infer_type \<Gamma> A = Some T \<and> ptrm_infer_type \<Gamma> B = Some S" by auto
qed

lemma infer_fstE:
  assumes "infer \<Gamma> (Fst P) = Some \<tau>"
  shows "\<exists>T S. infer \<Gamma> P = Some (TPair T S) \<and> \<tau> = T"
using assms proof(transfer)
  fix P :: "'a ptrm" and \<Gamma> \<tau>
  assume H: "ptrm_infer_type \<Gamma> (PFst P) = Some \<tau>"

  have "ptrm_infer_type \<Gamma> P \<noteq> None"
  proof(rule classical, auto)
    assume "ptrm_infer_type \<Gamma> P = None"
    thus False using H by simp
  qed
  moreover have "ptrm_infer_type \<Gamma> P \<noteq> Some TUnit"
  proof(rule classical, auto)
    assume "ptrm_infer_type \<Gamma> P = Some TUnit"
    thus False using H by simp
  qed
  moreover have "ptrm_infer_type \<Gamma> P \<noteq> Some (TVar x)" for x
  proof(rule classical, auto)
    assume "ptrm_infer_type \<Gamma> P = Some (TVar x)"
    thus False using H by simp
  qed
  moreover have "ptrm_infer_type \<Gamma> P \<noteq> Some (TArr T S)" for T S
  proof(rule classical, auto)
    assume "ptrm_infer_type \<Gamma> P = Some (TArr T S)"
    thus False using H by simp
  qed
  ultimately obtain T S where
    "ptrm_infer_type \<Gamma> P = Some (TPair T S)"
    using type.distinct type.exhaust option.exhaust by metis
  moreover hence "ptrm_infer_type \<Gamma> (PFst P) = Some T" by simp
  ultimately show "\<exists>T S. ptrm_infer_type \<Gamma> P = Some (TPair T S) \<and> \<tau> = T"
    using H by auto
qed

lemma infer_sndE:
  assumes "infer \<Gamma> (Snd P) = Some \<tau>"
  shows "\<exists>T S. infer \<Gamma> P = Some (TPair T S) \<and> \<tau> = S"
using assms proof(transfer)
  fix P :: "'a ptrm" and \<Gamma> \<tau>
  assume H: "ptrm_infer_type \<Gamma> (PSnd P) = Some \<tau>"

  have "ptrm_infer_type \<Gamma> P \<noteq> None"
  proof(rule classical, auto)
    assume "ptrm_infer_type \<Gamma> P = None"
    thus False using H by simp
  qed
  moreover have "ptrm_infer_type \<Gamma> P \<noteq> Some TUnit"
  proof(rule classical, auto)
    assume "ptrm_infer_type \<Gamma> P = Some TUnit"
    thus False using H by simp
  qed
  moreover have "ptrm_infer_type \<Gamma> P \<noteq> Some (TVar x)" for x
  proof(rule classical, auto)
    assume "ptrm_infer_type \<Gamma> P = Some (TVar x)"
    thus False using H by simp
  qed
  moreover have "ptrm_infer_type \<Gamma> P \<noteq> Some (TArr T S)" for T S
  proof(rule classical, auto)
    assume "ptrm_infer_type \<Gamma> P = Some (TArr T S)"
    thus False using H by simp
  qed
  ultimately obtain T S where
    "ptrm_infer_type \<Gamma> P = Some (TPair T S)"
    using type.distinct type.exhaust option.exhaust by metis
  moreover hence "ptrm_infer_type \<Gamma> (PSnd P) = Some S" by simp
  ultimately show "\<exists>T S. ptrm_infer_type \<Gamma> P = Some (TPair T S) \<and> \<tau> = S"
    using H by auto
qed

lemma infer_sound:
  assumes "infer \<Gamma> M = Some \<tau>"
  shows "\<Gamma> \<turnstile> M : \<tau>"
using assms proof(induction M arbitrary: \<Gamma> \<tau> rule: trm_induct)
  case 1
    thus ?case using infer_unitE typing.tunit by metis
  next
  case (2 x)
    hence "\<Gamma> x = Some \<tau>" using infer_varE by metis
    thus ?case using typing.tvar by metis
  next
  case (3 A B)
    from `infer \<Gamma> (App A B) = Some \<tau>` obtain \<sigma>
      where "infer \<Gamma> A = Some (TArr \<sigma> \<tau>)" and "infer \<Gamma> B = Some \<sigma>"
      using infer_appE by metis
    thus ?case using "3.IH" typing.tapp by metis
  next
  case (4 x T A \<Gamma> \<tau>)
    from `infer \<Gamma> (Fn x T A) = Some \<tau>` obtain \<sigma>
      where "\<tau> = TArr T \<sigma>" and "infer (\<Gamma>(x \<mapsto> T)) A = Some \<sigma>"
      using infer_fnE by metis
    thus ?case using "4.IH" typing.tfn by metis
  next
  case (5 A B \<Gamma> \<tau>)
    thus ?case using typing.tpair infer_pairE by metis
  next
  case (6 P \<Gamma> \<tau>)
    thus ?case using typing.tfst infer_fstE by metis
  next
  case (7 P \<Gamma> \<tau>)
    thus ?case using typing.tsnd infer_sndE by metis
  next
qed

lemma infer_complete:
  assumes "\<Gamma> \<turnstile> M : \<tau>"
  shows "infer \<Gamma> M = Some \<tau>"
using assms proof(induction arbitrary: \<Gamma> \<tau> rule: trm_induct)
  case 1
    thus ?case using typing_unitE infer_simp(1) by metis
  next
  next
  case (2 x)
    hence "\<Gamma> x = Some \<tau>" using typing_varE by metis
    thus ?case by(transfer, simp)
  next
  case (3 A B)
    from this obtain \<sigma> where "\<Gamma> \<turnstile> A : (TArr \<sigma> \<tau>)" "\<Gamma> \<turnstile> B : \<sigma>" using typing_appE by metis
    hence "infer \<Gamma> A = Some (TArr \<sigma> \<tau>)" and "infer \<Gamma> B = Some \<sigma>" using "3.IH" by auto
    thus ?case by(transfer, simp)
  next
  case (4 x T A \<Gamma> S)
    from this obtain \<sigma> where S: "S = TArr T \<sigma>" and "\<Gamma>(x \<mapsto> T) \<turnstile> A : \<sigma>" using typing_fnE by metis
    hence "infer (\<Gamma>(x \<mapsto> T)) A = Some \<sigma>" using "4.IH" by auto
    thus ?case using S by(transfer, simp)
  next
  case (5 A B \<Gamma> \<tau>)
    thus ?case using typing_pairE infer_simp(5) option.simps(5) old.prod.case by metis
  next
  case (6 P \<Gamma> \<tau>)
    thus ?case using typing_fstE infer_simp(6) by fastforce
  next
  case (7 P \<Gamma> \<sigma>)
    thus ?case using typing_sndE infer_simp(7) by fastforce
  next
qed

theorem infer_valid:
  shows "(\<Gamma> \<turnstile> M : \<tau>) = (infer \<Gamma> M = Some \<tau>)"
using infer_sound infer_complete by blast


inductive substitutes :: "'a trm \<Rightarrow> 'a \<Rightarrow> 'a trm \<Rightarrow> 'a trm \<Rightarrow> bool" where
  unit: "substitutes Unit y M Unit"
| var1: "x = y \<Longrightarrow> substitutes (Var x) y M M"
| var2: "x \<noteq> y \<Longrightarrow> substitutes (Var x) y M (Var x)"
| app:  "\<lbrakk>substitutes A x M A'; substitutes B x M B'\<rbrakk> \<Longrightarrow> substitutes (App A B) x M (App A' B')"
| fn:   "\<lbrakk>x \<noteq> y; y \<notin> fvs M; substitutes A x M A'\<rbrakk> \<Longrightarrow> substitutes (Fn y T A) x M (Fn y T A')"
| pair: "\<lbrakk>substitutes A x M A'; substitutes B x M B'\<rbrakk> \<Longrightarrow> substitutes (Pair A B) x M (Pair A' B')"
| fst:  "substitutes P x M P' \<Longrightarrow> substitutes (Fst P) x M (Fst P')"
| snd:  "substitutes P x M P' \<Longrightarrow> substitutes (Snd P) x M (Snd P')"

lemma substitutes_prm:
  assumes "substitutes A x M A'"
  shows "substitutes (\<pi> \<cdot> A) (\<pi> $ x) (\<pi> \<cdot> M) (\<pi> \<cdot> A')"
using assms proof(induction)
  case (unit y M)
    thus ?case using substitutes.unit trm_prm_simp(1) by metis
  case (var1 x y M)
    thus ?case using substitutes.var1 trm_prm_simp(2) by metis
  next
  case (var2 x y M)
    thus ?case using substitutes.var2 trm_prm_simp(2) prm_apply_unequal by metis
  next
  case (app A x M A' B B')
    thus ?case using substitutes.app trm_prm_simp(3) by metis
  next
  case (fn x y M A A' T)
    thus ?case
      using substitutes.fn trm_prm_simp(4) prm_apply_unequal prm_set_notmembership trm_prm_fvs
      by metis
  next
  case (pair A x M A' B B')
    thus ?case using substitutes.pair trm_prm_simp(5) by metis
  next
  case (fst P x M P')
    thus ?case using substitutes.fst trm_prm_simp(6) by metis
  next
  case (snd P x M P')
    thus ?case using substitutes.snd trm_prm_simp(7) by metis
  next
qed

lemma substitutes_fvs:
  assumes "substitutes A x M A'"
  shows "fvs A' \<subseteq> fvs A - {x} \<union> fvs M"
using assms proof(induction)
  case (unit y M)
    thus ?case using fvs_simp(1) by auto
  case (var1 x y M)
    thus ?case by auto
  next
  case (var2 x y M)
    thus ?case
      using fvs_simp(2) Un_subset_iff Un_upper2 insert_Diff_if insert_is_Un singletonD sup_commute
      by metis
  next
  case (app A x M A' B B')
    hence "fvs A' \<union> fvs B' \<subseteq> (fvs A - {x} \<union> fvs M) \<union> (fvs B - {x} \<union> fvs M)" by auto
    hence "fvs A' \<union> fvs B' \<subseteq> (fvs A \<union> fvs B) - {x} \<union> fvs M" by auto
    thus ?case using fvs_simp(3) by metis
  next
  case (fn x y M A A' T)
    hence "fvs A' - {y} \<subseteq> fvs A - {y} - {x} \<union> fvs M" by auto
    thus ?case using fvs_simp(4) by metis
  next
  case (pair A x M A' B B')
    hence "fvs A' \<union> fvs B' \<subseteq> (fvs A - {x} \<union> fvs M) \<union> (fvs B - {x} \<union> fvs M)" by auto
    hence "fvs A' \<union> fvs B' \<subseteq> (fvs A \<union> fvs B) - {x} \<union> fvs M" by auto
    thus ?case using fvs_simp(5) by metis
  next
  case (fst P x M P')
    thus ?case using fvs_simp(6) by fastforce
  next
  case (snd P x M P')
    thus ?case using fvs_simp(7) by fastforce
  next
qed

inductive_cases substitutes_unitE': "substitutes Unit y M X"
lemma substitutes_unitE:
  assumes "substitutes Unit y M X"
  shows "X = Unit"
by(
  rule substitutes_unitE'[where y=y and M=M and X=X],
  metis assms,
  auto simp add: unit_not_var unit_not_app unit_not_fn unit_not_pair unit_not_fst unit_not_snd
)

inductive_cases substitutes_varE': "substitutes (Var x) y M X"
lemma substitutes_varE:
  assumes "substitutes (Var x) y M X"
  shows "(x = y \<and> M = X) \<or> (x \<noteq> y \<and> X = Var x)"
by(
  rule substitutes_varE'[where x=x and y=y and M=M and X=X],
  metis assms,
  metis unit_not_var,
  metis trm_simp(1),
  metis trm_simp(1),
  auto simp add: var_not_app var_not_fn var_not_pair var_not_fst var_not_snd
)

inductive_cases substitutes_appE': "substitutes (App A B) x M X"
lemma substitutes_appE:
  assumes "substitutes (App A B) x M X"
  shows "\<exists>A' B'. substitutes A x M A' \<and> substitutes B x M B' \<and> X = App A' B'"
by(
  cases rule: substitutes_appE'[where A=A and B=B and x=x and M=M and X=X],
  metis assms,
  metis unit_not_app,
  metis var_not_app,
  metis var_not_app,
  metis trm_simp(2,3),
  auto simp add: app_not_fn app_not_pair app_not_fst app_not_snd
)

inductive_cases substitutes_fnE': "substitutes (Fn y T A) x M X"
lemma substitutes_fnE:
  assumes "substitutes (Fn y T A) x M X" "y \<noteq> x" "y \<notin> fvs M"
  shows "\<exists>A'. substitutes A x M A' \<and> X = Fn y T A'"
using assms
  apply (induction rule: substitutes_fnE'[where y=y and T=T and A=A and x=x and M=M and X=X])
  apply (metis assms(1))
  apply (metis unit_not_fn, metis var_not_fn, metis var_not_fn, metis app_not_fn)
  defer
  apply (metis fn_not_pair, metis fn_not_fst, metis fn_not_snd)
proof -
  case (6 z B B' S)
    consider "y = z \<and> T = S \<and> A = B" | "y \<noteq> z \<and> T = S \<and> y \<notin> fvs B \<and> A = [y \<leftrightarrow> z] \<cdot> B"
      using `Fn y T A = Fn z S B` trm_simp(4) by metis
    thus ?case proof(cases)
      case 1
        thus ?thesis using 6 by metis
      next
      case 2
        hence "y \<noteq> z" "T = S" "y \<notin> fvs B" "A = [y \<leftrightarrow> z] \<cdot> B" by auto
        have "substitutes ([y \<leftrightarrow> z] \<cdot> B) ([y \<leftrightarrow> z] $ x) ([y \<leftrightarrow> z] \<cdot> M) ([y \<leftrightarrow> z] \<cdot> B')"
          using substitutes_prm `substitutes B x M B'` by metis
        hence "substitutes A ([y \<leftrightarrow> z] $ x) ([y \<leftrightarrow> z] \<cdot> M) ([y \<leftrightarrow> z] \<cdot> B')"
          using `A = [y \<leftrightarrow> z] \<cdot> B` by metis
        hence "substitutes A x ([y \<leftrightarrow> z] \<cdot> M) ([y \<leftrightarrow> z] \<cdot> B')"
          using `y \<noteq> x` `x \<noteq> z` prm_unit_inaction by metis
        hence *: "substitutes A x M ([y \<leftrightarrow> z] \<cdot> B')"
          using `y \<notin> fvs M` `z \<notin> fvs M` trm_prm_unit_inaction by metis

        have "y \<notin> fvs B'"
          using
            substitutes_fvs `substitutes B x M B'` `y \<notin> fvs B` `y \<notin> fvs M`
            Diff_subset UnE set_rev_mp
          by blast
        hence "X = Fn y T ([y \<leftrightarrow> z] \<cdot> B')"
          using `X = Fn z S B'` `y \<noteq> z` `T = S` fn_eq
          by metis

        thus ?thesis using * by auto
      next
    qed      
  next
qed

inductive_cases substitutes_pairE': "substitutes (Pair A B) x M X"
lemma substitutes_pairE:
  assumes "substitutes (Pair A B) x M X"
  shows "\<exists>A' B'. substitutes A x M A' \<and> substitutes B x M B' \<and> X = Pair A' B'"
  apply (cases rule: substitutes_pairE'[where A=A and B=B and x=x and M=M and X=X])
  apply (metis assms)
  apply (metis unit_not_pair, metis var_not_pair, metis var_not_pair, metis app_not_pair, metis fn_not_pair)
  defer
  apply (metis pair_not_fst, metis pair_not_snd)
proof -
  case (7 A A' B B')
    thus ?thesis using trm_simp(5) trm_simp(6) by blast
  next
qed

inductive_cases substitutes_fstE': "substitutes (Fst P) x M X"
lemma substitutes_fstE:
  assumes "substitutes (Fst P) x M X"
  shows "\<exists>P'. substitutes P x M P' \<and> X = Fst P'"
  apply (cases rule: substitutes_fstE'[where P=P and x=x and M=M and X=X])
  apply (metis assms)
  apply (metis unit_not_fst, metis var_not_fst, metis var_not_fst, metis app_not_fst, metis fn_not_fst, metis pair_not_fst)
  defer
  apply (metis fst_not_snd)
proof -
  case (8 P P')
    thus ?thesis using trm_simp(7) by blast
  next
qed

inductive_cases substitutes_sndE': "substitutes (Snd P) x M X"
lemma substitutes_sndE:
  assumes "substitutes (Snd P) x M X"
  shows "\<exists>P'. substitutes P x M P' \<and> X = Snd P'"
  apply (cases rule: substitutes_sndE'[where P=P and x=x and M=M and X=X])
  apply (metis assms)
  apply (metis unit_not_snd, metis var_not_snd, metis var_not_snd, metis app_not_snd, metis fn_not_snd, metis pair_not_snd, metis fst_not_snd)
proof -
  case (9 P P')
    thus ?thesis using trm_simp(8) by blast
  next
qed

lemma substitutes_total:
  shows "\<exists>X. substitutes A x M X"
proof(induction "{x} \<union> fvs M" A rule: trm_strong_induct)
  show "finite ({x} \<union> fvs M)" using fvs_finite by auto
  next

  fix y
  show "\<exists>X. substitutes Unit y M X"
  proof -
    obtain X :: "'a trm" where "X = Unit" by auto
    thus ?thesis using substitutes.unit by metis
  qed
  next

  fix y
  show "\<exists>X. substitutes (Var y) x M X"
  proof -
    consider "x = y" | "x \<noteq> y" by auto
    thus ?thesis proof(cases)
      case 1
        obtain X where "X = M" by auto
        hence "substitutes (Var y) x M X" using `x = y` substitutes.var1 by metis
        thus ?thesis by auto
      next
      case 2
        obtain X where "X = (Var y)" by auto
        hence "substitutes (Var y) x M X" using `x \<noteq> y` substitutes.var2 by metis
        thus ?thesis by auto
      next
    qed
  qed
  next

  fix A B
  assume "\<exists>A'. substitutes A x M A'" and "\<exists>B'. substitutes B x M B'"
  from this obtain A' B' where A': "substitutes A x M A'" and B': "substitutes B x M B'" by auto
  show "\<exists>X. substitutes (App A B) x M X"
  proof -
    obtain X where "X = App A' B'" by auto
    hence "substitutes (App A B) x M X" using A' B' substitutes.app by metis
    thus ?thesis by auto
  qed
  next

  fix y T A
  assume "y \<notin> ({x} \<union> fvs M)" and "\<exists>A'. substitutes A x M A'"
  from this obtain A' where A': "substitutes A x M A'" by auto
  from `y \<notin> ({x} \<union> fvs M)` have "y \<noteq> x" "y \<notin> fvs M" by auto
  show "\<exists>X. substitutes (Fn y T A) x M X"
  proof -
    obtain X where "X = Fn y T A'" by auto
    hence "substitutes (Fn y T A) x M X" using substitutes.fn `y \<noteq> x` `y \<notin> fvs M` A' by metis
    thus ?thesis by auto
  qed
  next

  fix A B
  assume "\<exists>A'. substitutes A x M A'" "\<exists>B'. substitutes B x M B'"
  from this obtain A' B' where "substitutes A x M A'" "substitutes B x M B'" by auto
  from this obtain X where "X = Pair A' B'" by auto
  hence "substitutes (Pair A B) x M X"
    using substitutes.pair `substitutes A x M A'` `substitutes B x M B'`
    by metis
  thus "\<exists>X. substitutes (Pair A B) x M X" by auto
  next

  fix P
  assume "\<exists>P'. substitutes P x M P'"
  from this obtain P' where "substitutes P x M P'" by auto
  from this obtain X where "X = Fst P'" by auto
  hence "substitutes (Fst P) x M X" using substitutes.fst `substitutes P x M P'` by metis
  thus "\<exists>X. substitutes (Fst P) x M X" by auto
  next

  fix P
  assume "\<exists>P'. substitutes P x M P'"
  from this obtain P' where "substitutes P x M P'" by auto
  from this obtain X where "X = Snd P'" by auto
  hence "substitutes (Snd P) x M X" using substitutes.snd `substitutes P x M P'` by metis
  thus "\<exists>X. substitutes (Snd P) x M X" by auto
  next
qed

lemma substitutes_unique:
  assumes "substitutes A x M B" "substitutes A x M C"
  shows "B = C"
using assms proof(induction A arbitrary: B C rule: trm_strong_induct[where S="{x} \<union> fvs M"])
  show "finite ({x} \<union> fvs M)" using fvs_finite by auto
  next

  case 1
    thus ?case using substitutes_unitE by metis
  next
  case (2 y)
    thus ?case using substitutes_varE by metis
  next
  case (3 X Y)
    thus ?case using substitutes_appE by metis
  next
  case (4 y T A)
    hence "y \<noteq> x" and "y \<notin> fvs M" by auto
    thus ?case using 4 substitutes_fnE by metis
  next
  case (5 A B C D)
    thus ?case using substitutes_pairE by metis
  next
  case (6 P Q R)
    thus ?case using substitutes_fstE by metis
  next
  case (7 P Q R)
    thus ?case using substitutes_sndE by metis
  next
qed

lemma substitutes_function:
  shows "\<exists>! X. substitutes A x M X"
using substitutes_total substitutes_unique by metis

definition subst :: "'a trm \<Rightarrow> 'a \<Rightarrow> 'a trm \<Rightarrow> 'a trm" ("_[_ ::= _]") where
  "subst A x M \<equiv> (THE X. substitutes A x M X)"

lemma subst_simp_unit:
  shows "Unit[x ::= M] = Unit"
unfolding subst_def by(rule, metis substitutes.unit, metis substitutes_function substitutes.unit)

lemma subst_simp_var1:
  shows "(Var x)[x ::= M] = M"
unfolding subst_def by(rule, metis substitutes.var1, metis substitutes_function substitutes.var1)

lemma subst_simp_var2:
  assumes "x \<noteq> y"
  shows "(Var x)[y ::= M] = Var x"
unfolding subst_def by(
  rule,
  metis substitutes.var2 assms,
  metis substitutes_function substitutes.var2 assms
)

lemma subst_simp_app:
  shows "(App A B)[x ::= M] = App (A[x ::= M]) (B[x ::= M])"
unfolding subst_def proof
  obtain A' B' where A': "A' = (A[x ::= M])" and B': "B' = (B[x ::= M])" by auto
  hence "substitutes A x M A'" "substitutes B x M B'"
    unfolding subst_def
    using substitutes_function theI by metis+
  hence "substitutes (App A B) x M (App A' B')" using substitutes.app by metis
  thus *: "substitutes (App A B) x M (App (THE X. substitutes A x M X) (THE X. substitutes B x M X))"
    using A' B' unfolding subst_def by metis

  fix X
  assume "substitutes (App A B) x M X"
  thus "X = App (THE X. substitutes A x M X) (THE X. substitutes B x M X)"
    using substitutes_function * by metis
qed

lemma subst_simp_fn:
  assumes "x \<noteq> y" "y \<notin> fvs M"
  shows "(Fn y T A)[x ::= M] = Fn y T (A[x ::= M])"
unfolding subst_def proof
  obtain A' where A': "A' = (A[x ::= M])" by auto
  hence "substitutes A x M A'" unfolding subst_def using substitutes_function theI by metis
  hence "substitutes (Fn y T A) x M (Fn y T A')" using substitutes.fn assms by metis
  thus *: "substitutes (Fn y T A) x M (Fn y T (THE X. substitutes A x M X))"
    using A' unfolding subst_def by metis

  fix X
  assume "substitutes (Fn y T A) x M X"
  thus "X = Fn y T (THE X. substitutes A x M X)" using substitutes_function * by metis
qed

lemma subst_simp_pair:
  shows "(Pair A B)[x ::= M] = Pair (A[x ::= M]) (B[x ::= M])"
unfolding subst_def proof
  obtain A' B' where A': "A' = (A[x ::= M])" and B': "B' = (B[x ::= M])" by auto
  hence "substitutes A x M A'" "substitutes B x M B'"
    unfolding subst_def using substitutes_function theI by metis+
  hence "substitutes (Pair A B) x M (Pair A' B')" using substitutes.pair assms by metis
  thus *: "substitutes (Pair A B) x M (Pair (THE X. substitutes A x M X) (THE X. substitutes B x M X))"
    using A' B' unfolding subst_def by metis

  fix X
  assume "substitutes (Pair A B) x M X"
  thus "X = Pair (THE X. substitutes A x M X) (THE X. substitutes B x M X)"
    using substitutes_function * by metis
qed

lemma subst_simp_fst:
  shows "(Fst P)[x ::= M] = Fst (P[x ::= M])"
unfolding subst_def proof
  obtain P' where P': "P' = (P[x ::= M])" by auto
  hence "substitutes P x M P'" unfolding subst_def using substitutes_function theI by metis
  hence "substitutes (Fst P) x M (Fst P')" using substitutes.fst by metis
  thus *: "substitutes (Fst P) x M (Fst (THE X. substitutes P x M X))"
    using P' unfolding subst_def by metis

  fix X
  assume "substitutes (Fst P) x M X"
  thus "X = Fst (THE X. substitutes P x M X)" using substitutes_function * by metis
qed

lemma subst_simp_snd:
  shows "(Snd P)[x ::= M] = Snd (P[x ::= M])"
unfolding subst_def proof
  obtain P' where P': "P' = (P[x ::= M])" by auto
  hence "substitutes P x M P'" unfolding subst_def using substitutes_function theI by metis
  hence "substitutes (Snd P) x M (Snd P')" using substitutes.snd by metis
  thus *: "substitutes (Snd P) x M (Snd (THE X. substitutes P x M X))"
    using P' unfolding subst_def by metis

  fix X
  assume "substitutes (Snd P) x M X"
  thus "X = Snd (THE X. substitutes P x M X)" using substitutes_function * by metis
qed

lemma subst_prm:
  shows "(\<pi> \<cdot> (M[z ::= N])) = ((\<pi> \<cdot> M)[\<pi> $ z ::= \<pi> \<cdot> N])"
unfolding subst_def using substitutes_prm substitutes_function the1_equality by (metis (full_types))

lemma subst_fvs:
  shows "fvs (M[z ::= N]) \<subseteq> (fvs M - {z}) \<union> fvs N"
unfolding subst_def using substitutes_fvs substitutes_function theI2 by metis

lemma typing_subst:
  assumes "\<Gamma>(z \<mapsto> \<tau>) \<turnstile> M : \<sigma>" "\<Gamma> \<turnstile> N : \<tau>"
  shows "\<Gamma> \<turnstile> M[z ::= N] : \<sigma>"
using assms proof(induction M arbitrary: \<Gamma> \<sigma> rule: trm_strong_depth_induct[where S="{z} \<union> fvs N"])
  show "finite ({z} \<union> fvs N)" using fvs_finite by auto
  next

  case 1
    thus ?case using subst_simp_unit typing.tunit typing_unitE by metis
  next
  case (2 x)
    hence *: "(\<Gamma>(z \<mapsto> \<tau>)) x = Some \<sigma>" using typing_varE by metis

    consider "x = z" | "x \<noteq> z" by auto
    thus ?case proof(cases)
      case 1
        hence "(\<Gamma>(x \<mapsto> \<tau>)) x = Some \<sigma>" using * by metis
        hence "\<tau> = \<sigma>" by auto
        thus ?thesis using `\<Gamma> \<turnstile> N : \<tau>` subst_simp_var1 `x = z` by metis
      next
      case 2
        hence "\<Gamma> x = Some \<sigma>" using * by auto
        hence "\<Gamma> \<turnstile> Var x : \<sigma>" using typing.tvar by metis
        thus ?thesis using `x \<noteq> z` subst_simp_var2 by metis
      next
    qed
  next
  case (3 A B)
    have *: "depth A < depth (App A B) \<and> depth B < depth (App A B)"
      using depth_app by auto

    from `\<Gamma>(z \<mapsto> \<tau>) \<turnstile> App A B : \<sigma>` obtain \<sigma>' where
      "\<Gamma>(z \<mapsto> \<tau>) \<turnstile> A : (TArr \<sigma>' \<sigma>)"
      "\<Gamma>(z \<mapsto> \<tau>) \<turnstile> B : \<sigma>'"
      using typing_appE by metis
    hence
      "\<Gamma> \<turnstile> (A[z ::= N]) : (TArr \<sigma>' \<sigma>)"
      "\<Gamma> \<turnstile> (B[z ::= N]) : \<sigma>'"
      using 3 * by metis+
    hence "\<Gamma> \<turnstile> App (A[z ::= N]) (B[z ::= N]) : \<sigma>" using typing.tapp by metis
    thus ?case using subst_simp_app by metis
  next
  case (4 x T A)
    hence "x \<noteq> z" "x \<notin> fvs N" by auto
    hence *: "\<Gamma>(x \<mapsto> T) \<turnstile> N : \<tau>" using typing_weaken 4 by metis
    have **: "depth A < depth (Fn x T A)" using depth_fn.

    from `\<Gamma>(z \<mapsto> \<tau>) \<turnstile> Fn x T A : \<sigma>` obtain \<sigma>' where
      "\<sigma> = TArr T \<sigma>'"
      "\<Gamma>(z \<mapsto> \<tau>)(x \<mapsto> T) \<turnstile> A : \<sigma>'"
      using typing_fnE by metis
    hence "\<Gamma>(x \<mapsto> T)(z \<mapsto> \<tau>) \<turnstile> A : \<sigma>'" using `x \<noteq> z` fun_upd_twist by metis
    hence "\<Gamma>(x \<mapsto> T) \<turnstile> A[z ::= N] : \<sigma>'" using 4 * ** by metis
    hence "\<Gamma> \<turnstile> Fn x T (A[z ::= N]) : \<sigma>" using typing.tfn `\<sigma> = TArr T \<sigma>'` by metis
    thus ?case using `x \<noteq> z` `x \<notin> fvs N` subst_simp_fn by metis
  next
qed


inductive beta_reduction :: "'a trm \<Rightarrow> 'a trm \<Rightarrow> bool" ("_ \<rightarrow>\<beta> _") where
  beta: "(App (Fn x T A) M) \<rightarrow>\<beta> (A[x ::= M])"
| app1: "A \<rightarrow>\<beta> A' \<Longrightarrow> (App A B) \<rightarrow>\<beta> (App A' B)"
| app2: "B \<rightarrow>\<beta> B' \<Longrightarrow> (App A B) \<rightarrow>\<beta> (App A B')"
| fn:   "A \<rightarrow>\<beta> A' \<Longrightarrow> (Fn x T A) \<rightarrow>\<beta> (Fn x T A')"

lemma beta_reduction_fvs:
  assumes "M \<rightarrow>\<beta> M'"
  shows "fvs M' \<subseteq> fvs M"
using assms proof(induction)
  case (beta x T A M)
    thus ?case using fvs_simp(3) fvs_simp(4) subst_fvs by metis
  next
  case (app1 A A' B)
    hence "fvs A' \<union> fvs B \<subseteq> fvs A \<union> fvs B" by auto
    thus ?case using fvs_simp(3) by metis
  next
  case (app2 B B' A)
    hence "fvs A \<union> fvs B' \<subseteq> fvs A \<union> fvs B" by auto
    thus ?case using fvs_simp(3) by metis
  next
  case (fn A A' x T)
    hence "fvs A' - {x} \<subseteq> fvs A - {x}" by auto
    thus ?case using fvs_simp(4) by metis
  next
qed

lemma beta_reduction_prm:
  assumes "M \<rightarrow>\<beta> M'"
  shows "(\<pi> \<cdot> M) \<rightarrow>\<beta> (\<pi> \<cdot> M')"
using assms proof(induction)
  case (beta x T A M)
    thus ?case using beta_reduction.beta trm_prm_simp(3) trm_prm_simp(4) subst_prm by metis
  next
  case (app1 A A' B)
    thus ?case using beta_reduction.app1 trm_prm_simp(3) by metis
  next
  case (app2 B B' A)
    thus ?case using beta_reduction.app2 trm_prm_simp(3) by metis
  next
  case (fn A A' x T)
    thus ?case using beta_reduction.fn trm_prm_simp(4) by metis
  next
qed

lemma beta_reduction_left_unitE:
  assumes "Unit \<rightarrow>\<beta> M'"
  shows "False"
using assms by(cases, auto simp add: unit_not_app unit_not_fn)

lemma beta_reduction_left_varE:
  assumes "(Var x) \<rightarrow>\<beta> M'"
  shows "False"
using assms by(cases, auto simp add: var_not_app var_not_fn)

lemma beta_reduction_left_appE:
  assumes "(App A B) \<rightarrow>\<beta> M'"
  shows "
    (\<exists>x T X. A = (Fn x T X) \<and> M' = (X[x ::= B])) \<or>
    (\<exists>A'. (A \<rightarrow>\<beta> A') \<and> M' = App A' B) \<or>
    (\<exists>B'. (B \<rightarrow>\<beta> B') \<and> M' = App A B')
  "
using assms by(
  cases,
  metis trm_simp(2, 3),
  metis trm_simp(2, 3),
  metis trm_simp(2, 3),
  metis app_not_fn
)

lemma beta_reduction_left_fnE:
  assumes "(Fn x T A) \<rightarrow>\<beta> M'"
  shows "\<exists>A'. (A \<rightarrow>\<beta> A') \<and> M' = (Fn x T A')"
using assms proof(cases, metis app_not_fn, metis app_not_fn, metis app_not_fn)
  case (fn B B' y S)
    consider "x = y \<and> T = S \<and> A = B" | "x \<noteq> y \<and> T = S \<and> x \<notin> fvs B \<and> A = [x \<leftrightarrow> y] \<cdot> B"
      using trm_simp(4) `Fn x T A = Fn y S B` by metis
    thus ?thesis proof(cases)
      case 1
        thus ?thesis using fn by auto
      next
      case 2
        thus ?thesis using fn beta_reduction_fvs beta_reduction_prm fn_eq by fastforce
      next
    qed
  next
qed

lemma preservation':
  assumes "\<Gamma> \<turnstile> M : \<tau>" and "M \<rightarrow>\<beta> M'"
  shows "\<Gamma> \<turnstile> M' : \<tau>"
using assms proof(induction arbitrary: M' rule: typing.induct)
  case (tunit \<Gamma>)
    thus ?case using beta_reduction_left_unitE by metis
  next
  case (tvar \<Gamma> x \<tau>)
    thus ?case using beta_reduction_left_varE by metis
  next
  case (tapp \<Gamma> A \<tau> \<sigma> B M')
    from `(App A B) \<rightarrow>\<beta> M'` consider
      "(\<exists>x T X. A = (Fn x T X) \<and> M' = (X[x ::= B]))" |
      "(\<exists>A'. (A \<rightarrow>\<beta> A') \<and> M' = App A' B)" |
      "(\<exists>B'. (B \<rightarrow>\<beta> B') \<and> M' = App A B')" using beta_reduction_left_appE by metis

    thus ?case proof(cases)
      case 1
        from this obtain x T X where "A = Fn x T X" and *: "M' = (X[x ::= B])" by auto

        have "\<Gamma>(x \<mapsto> \<tau>) \<turnstile> X : \<sigma>" using typing_fnE `\<Gamma> \<turnstile> A : (TArr \<tau> \<sigma>)` `A = Fn x T X` type.inject
          by blast
        hence "\<Gamma> \<turnstile> (X[x ::= B]) : \<sigma>" using typing_subst `\<Gamma> \<turnstile> B : \<tau>` by metis
        thus ?thesis using * by auto
      next
      case 2
        from this obtain A' where "A \<rightarrow>\<beta> A'" and *: "M' = (App A' B)" by auto
        hence "\<Gamma> \<turnstile> A' : (TArr \<tau> \<sigma>)" using tapp.IH(1) by metis
        hence "\<Gamma> \<turnstile> (App A' B) : \<sigma>" using `\<Gamma> \<turnstile> B : \<tau>` typing.tapp by metis
        thus ?thesis using * by auto
      next
      case 3
        from this obtain B' where "B \<rightarrow>\<beta> B'" and *: "M' = (App A B')" by auto
        hence "\<Gamma> \<turnstile> B' : \<tau>" using tapp.IH(2) by metis
        hence "\<Gamma> \<turnstile> (App A B') : \<sigma>" using `\<Gamma> \<turnstile> A : (TArr \<tau> \<sigma>)` typing.tapp by metis
        thus ?thesis using * by auto
      next
    qed
  next
  case (tfn \<Gamma> x T A \<sigma>)
    from this obtain A' where "A \<rightarrow>\<beta> A'" and *: "M' = (Fn x T A')"
      using beta_reduction_left_fnE by metis
    hence "\<Gamma>(x \<mapsto> T) \<turnstile> A' : \<sigma>" using tfn.IH by metis
    hence "\<Gamma> \<turnstile> (Fn x T A') : (TArr T \<sigma>)" using typing.tfn by metis
    thus ?case using * by auto
  next
qed

inductive NF :: "'a trm \<Rightarrow> bool" where
  unit: "NF Unit"
| var: "NF (Var x)"
| app_var: "NF B \<Longrightarrow> NF (App (Var x) B)"
| app_app: "\<lbrakk>NF (App C D); NF B\<rbrakk> \<Longrightarrow> NF (App (App C D) B)"
| fn: "NF A \<Longrightarrow> NF (Fn x T A)"

theorem progress:
  assumes "\<Gamma> \<turnstile> M : \<tau>"
  shows "NF M \<or> (\<exists>M'. (M \<rightarrow>\<beta> M'))"
using assms proof(induction M arbitrary: \<Gamma> \<tau> rule: trm_induct)
  case 1
    thus ?case using NF.unit by metis
  next
  case (2 x)
    thus ?case using NF.var by metis
  next
  case (3 A B)
    from `\<Gamma> \<turnstile> App A B : \<tau>` obtain \<sigma>
      where "\<Gamma> \<turnstile> A : (TArr \<sigma> \<tau>)" and "\<Gamma> \<turnstile> B : \<sigma>"
      using typing_appE by metis
    hence A: "NF A \<or> (\<exists>A'. (A \<rightarrow>\<beta> A'))" and B: "NF B \<or> (\<exists>B'. (B \<rightarrow>\<beta> B'))"
      using "3.IH" by auto

    consider "NF B" | "\<exists>B'. (B \<rightarrow>\<beta> B')" using B by auto
    thus ?case proof(cases)
      case 1
        consider "NF A" | "\<exists>A'. (A \<rightarrow>\<beta> A')" using A by auto
        thus ?thesis proof(cases)
          case 1
            thus ?thesis proof(induction A rule: trm_cases)
              case 1
                show ?thesis
                  using `A = Unit` `\<Gamma> \<turnstile> A : (TArr \<sigma> \<tau>)` type.distinct(3) typing_unitE
                  by metis
              next
              case (2 x)
                thus ?thesis using `NF B` NF.app_var by metis
              next
              case (3 C D)
                thus ?thesis using `NF B` NF.app_app by metis
              next
              case (4 y S X)
                hence "(App A B) \<rightarrow>\<beta> (X[y ::= B])" using beta_reduction.beta by metis
                thus ?thesis by auto
              next
            qed
          next
          case 2
            thus ?thesis using beta_reduction.app1 by metis
          next
        qed
      next
      case 2
        thus ?thesis using beta_reduction.app2 by metis
      next
    qed
  next
  case (4 x T A)
    from `\<Gamma> \<turnstile> Fn x T A : \<tau>` obtain \<sigma>
      where "\<tau> = TArr T \<sigma>" and "\<Gamma>(x \<mapsto> T) \<turnstile> A : \<sigma>"
      using typing_fnE by metis
    from `\<Gamma>(x \<mapsto> T) \<turnstile> A : \<sigma>` consider "NF A" | "\<exists>A'. (A \<rightarrow>\<beta> A')"
      using "4.IH" by metis

    thus ?case proof(cases)
      case 1
        thus ?thesis using NF.fn by metis
      next
      case 2
        from this obtain A' where "A \<rightarrow>\<beta> A'" by auto
        obtain M' where "M' = Fn x T A'" by auto
        hence "(Fn x T A) \<rightarrow>\<beta> M'" using `A \<rightarrow>\<beta> A'` beta_reduction.fn by metis
        thus ?thesis by auto
      next
    qed
  next
qed

inductive beta_reduces :: "'a trm \<Rightarrow> 'a trm \<Rightarrow> bool" ("_ \<rightarrow>\<beta>\<^sup>* _") where
  reflexive:  "M \<rightarrow>\<beta>\<^sup>* M"
| transitive: "\<lbrakk>M \<rightarrow>\<beta>\<^sup>* M'; M' \<rightarrow>\<beta> M''\<rbrakk> \<Longrightarrow> M \<rightarrow>\<beta>\<^sup>* M''"

lemma beta_reduces_composition:
  assumes "A' \<rightarrow>\<beta>\<^sup>* A''" and "A \<rightarrow>\<beta>\<^sup>* A'"
  shows "A \<rightarrow>\<beta>\<^sup>* A''"
using assms proof(induction)
  case (reflexive B)
    thus ?case.
  next
  case (transitive B B' B'')
    thus ?case using beta_reduces.transitive by metis
  next
qed

lemma beta_reduces_fvs:
  assumes "A \<rightarrow>\<beta>\<^sup>* A'"
  shows "fvs A' \<subseteq> fvs A"
using assms proof(induction)
  case (reflexive M)
    thus ?case by auto
  next
  case (transitive M M' M'')
    hence "fvs M'' \<subseteq> fvs M'" using beta_reduction_fvs by metis
    thus ?case using `fvs M' \<subseteq> fvs M` by auto
  next
qed

lemma beta_reduces_app_left:
  assumes "A \<rightarrow>\<beta>\<^sup>* A'"
  shows "(App A B) \<rightarrow>\<beta>\<^sup>* (App A' B)"
using assms proof(induction)
  case (reflexive A)
    thus ?case using beta_reduces.reflexive.
  next
  case (transitive A A' A'')
    thus ?case using beta_reduces.transitive beta_reduction.app1 by metis
  next
qed

lemma beta_reduces_app_right:
  assumes "B \<rightarrow>\<beta>\<^sup>* B'"
  shows "(App A B) \<rightarrow>\<beta>\<^sup>* (App A B')"
using assms proof(induction)
  case (reflexive B)
    thus ?case using beta_reduces.reflexive.
  next
  case (transitive B B' B'')
    thus ?case using beta_reduces.transitive beta_reduction.app2 by metis
  next
qed

lemma beta_reduces_fn:
  assumes "A \<rightarrow>\<beta>\<^sup>* A'"
  shows "(Fn x T A) \<rightarrow>\<beta>\<^sup>* (Fn x T A')"
using assms proof(induction)
  case (reflexive A)
    thus ?case using beta_reduces.reflexive.
  next
  case (transitive A A' A'')
    thus ?case using beta_reduces.transitive beta_reduction.fn by metis
  next
qed

theorem preservation:
  assumes "M \<rightarrow>\<beta>\<^sup>* M'" "\<Gamma> \<turnstile> M : \<tau>"
  shows "\<Gamma> \<turnstile> M' : \<tau>"
using assms proof(induction)
  case (reflexive M)
    thus ?case.
  next
  case (transitive M M' M'')
    thus ?case using preservation' by metis
  next
qed

theorem safety:
  assumes "M \<rightarrow>\<beta>\<^sup>* M'" "\<Gamma> \<turnstile> M : \<tau>"
  shows "NF M' \<or> (\<exists>M''. (M' \<rightarrow>\<beta> M''))"
using assms proof(induction)
  case (reflexive M)
    thus ?case using progress by metis
  next
  case (transitive M M' M'')
    hence "\<Gamma> \<turnstile> M' : \<tau>" using preservation by metis
    hence "\<Gamma> \<turnstile> M'' : \<tau>" using preservation' `M' \<rightarrow>\<beta> M''` by metis
    thus ?case using progress by metis
  next
qed


lemma substitution_inner:
  assumes "M \<rightarrow>\<beta>\<^sup>* M'"
  shows "(X[z ::= M]) \<rightarrow>\<beta>\<^sup>* (X[z ::= M'])"
using assms proof(induction X rule: trm_strong_induct[where S="{z} \<union> fvs M"])
  show "finite ({z} \<union> fvs M)" using fvs_finite by auto
  next

  case 1
    thus ?case using subst_simp_unit beta_reduces.reflexive by metis
  next
  case (2 x)
    thus ?case 
      by (cases "x = z", metis subst_simp_var1, metis subst_simp_var2 beta_reduces.reflexive)
  next
  case (3 A B)
    hence "(A[z ::= M]) \<rightarrow>\<beta>\<^sup>* (A[z ::= M'])" "(B[z ::= M]) \<rightarrow>\<beta>\<^sup>* (B[z ::= M'])" by auto
    hence "(App (A[z ::= M]) (B[z ::= M])) \<rightarrow>\<beta>\<^sup>* (App (A[z ::= M']) (B[z ::= M']))"
      using beta_reduces_app_left beta_reduces_app_right beta_reduces_composition by metis
    thus ?case using subst_simp_app by metis
  next
  case (4 x T A)
    hence "x \<noteq> z" "x \<notin> fvs M" "x \<notin> fvs M'" "(A[z ::= M]) \<rightarrow>\<beta>\<^sup>* (A[z ::= M'])"
      using beta_reduces_fvs by auto
    hence "(Fn x T (A[z ::= M])) \<rightarrow>\<beta>\<^sup>* (Fn x T (A[z ::= M']))"
      using beta_reduces_fn by metis
    thus ?case using subst_simp_fn `x \<noteq> z` `x \<notin> fvs M` `x \<notin> fvs M'` by metis
  next
qed

lemma substitution_outer':
  assumes "X \<rightarrow>\<beta> X'"
  shows "(X[z ::= M]) \<rightarrow>\<beta> (X'[z ::= M])"
using assms proof(induction X arbitrary: X' rule: trm_strong_induct[where S="{z} \<union> fvs M"])
  show "finite ({z} \<union> fvs M)" using fvs_finite by auto
  next

  case 1
    thus ?case using beta_reduction_left_unitE by metis
  next
  case (2 x)
    thus ?case using beta_reduction_left_varE by metis
  next
  case (4 x T B)
    hence "x \<noteq> z" and "x \<notin> fvs M" by auto
    from `(Fn x T B) \<rightarrow>\<beta> X'` obtain B' where "B \<rightarrow>\<beta> B'" "X' = Fn x T B'"
      using beta_reduction_left_fnE by metis
    thus ?case using "4.IH" beta_reduction.fn `x \<noteq> z` `x \<notin> fvs M` subst_simp_fn by auto
  next
  case (3 A B)
    from `(App A B) \<rightarrow>\<beta> X'` and beta_reduction_left_appE consider
      "\<exists>x T A'. A = Fn x T A' \<and> X' = (A'[x ::= B])"
    | "\<exists>A'. (A \<rightarrow>\<beta> A') \<and> X' = App A' B"
    | "\<exists>B'. (B \<rightarrow>\<beta> B') \<and> X' = App A B'" by metis
    thus ?case proof(cases)
      case 2
        from this obtain A' where "A \<rightarrow>\<beta> A'" "X' = App A' B" by auto
        thus ?thesis using subst_simp_app "3.IH" beta_reduction.app1 by metis
      next
      case 3
        from this obtain B' where "B \<rightarrow>\<beta> B'" "X' = App A B'" by auto
        thus ?thesis using subst_simp_app "3.IH" beta_reduction.app2 by metis
      next
      case 1
        thus ?thesis sorry
      next
    qed
  next
qed

lemma substitution_outer:
  assumes "A \<rightarrow>\<beta>\<^sup>* A'"
  shows "(A[x ::= X]) \<rightarrow>\<beta>\<^sup>* (A'[x ::= X])"
using assms proof(induction)
  case (reflexive A)
    thus ?case using beta_reduces.reflexive.
  next
  case (transitive A A' A'')
    thus ?case using substitution_outer' beta_reduces.transitive by metis
  next
qed

inductive parallel_reduction :: "'a trm \<Rightarrow> 'a trm \<Rightarrow> bool" ("_ >> _") where
  refl: "A >> A"
| beta: "\<lbrakk>A >> A'; B >> B'\<rbrakk> \<Longrightarrow> (App (Fn x T A) B) >> (A'[x ::= B'])"
| eta:  "A >> A' \<Longrightarrow> (Fn x T A) >> (Fn x T A')"
| app:  "\<lbrakk>A >> A'; B >> B'\<rbrakk> \<Longrightarrow> (App A B) >> (App A' B')"

inductive_cases parallel_reduction_unitE': "Unit >> A"
lemma parallel_reduction_unitE:
  assumes "Unit >> A"
  shows "A = Unit"
using assms by(rule parallel_reduction_unitE'[where A=A], auto simp add: unit_not_app unit_not_fn)

inductive_cases parallel_reduction_varE': "(Var x) >> A"
lemma parallel_reduction_varE:
  assumes "(Var x) >> A"
  shows "A = Var x"
using assms by(
  induction rule: parallel_reduction_varE'[where x=x and A=A],
  metis assms,
  metis,
  metis var_not_app,
  metis var_not_fn,
  metis var_not_app
)

inductive_cases parallel_reduction_redexE': "(App (Fn x T A) B) >> X"
lemma parallel_reduction_redexE:
  assumes "(App (Fn x T A) B) >> X"
  shows "
    (X = App (Fn x T A) B) \<or>
    ((A >> A') \<and> (B >> B') \<and> X = (A'[x ::= B'])) \<or>
    (((Fn x T A) >> (Fn x T A')) \<and> (B >> B') \<and> X = (App (Fn x T A') B'))
  "
sorry

inductive_cases parallel_reduction_fnE': "(Fn x T A) >> X"
lemma parallel_reduction_fnE:
  assumes "(Fn x T A) >> X"
  shows "X = Fn x T A \<or> (A >> A') \<and> X = Fn x T A'"
sorry

lemma parallel_reduction_nonredexE:
  assumes "(App A B) >> X" and "\<not>(\<exists>x T A'. A = Fn x T A')"
  shows "(A >> A') \<and> (B >> B') \<and> X = (App A' B')"
sorry

lemma parallel_reduction_prm:
  assumes "A >> A'"
  shows "(\<pi> \<cdot> A) >> (\<pi> \<cdot> A')"
using assms proof(induction)
  case (refl A)
    thus ?case using parallel_reduction.refl.
  next
  case (beta A A' B B' x T)
    thus ?case using parallel_reduction.beta subst_prm trm_prm_simp(3, 4) by metis
  next
  case (eta A A' x T)
    thus ?case using parallel_reduction.eta trm_prm_simp(4) by metis
  next
  case (app A A' B B')
    thus ?case using parallel_reduction.app trm_prm_simp(3) by metis
  next
qed

lemma parallel_reduction_fvs:
  assumes "A >> A'"
  shows "fvs A' \<subseteq> fvs A"
using assms proof(induction)
  case (refl A)
    thus ?case by auto
  next
  case (beta A A' B B' x T)
    have *:"fvs (App (Fn x T A) B) = fvs A - {x} \<union> fvs B" using fvs_simp(3, 4) by metis
    have "fvs (A'[x ::= B']) \<subseteq> fvs A' - {x} \<union> fvs B'" using subst_fvs.
    also have "... \<subseteq> fvs A - {x} \<union> fvs B" using beta.IH by auto
    finally show ?case using fvs_simp(3, 4) by metis
  next
  case (eta A A' x T)
    thus ?case using fvs_simp(4) Un_Diff subset_Un_eq by metis
  next
  case (app A A' B B')
    thus ?case using fvs_simp(3) Un_mono by metis
  next
qed

inductive complete_development :: "'a trm \<Rightarrow> 'a trm \<Rightarrow> bool" ("_ >>> _") where
  unit: "Unit >>> Unit"
| var:  "(Var x) >>> (Var x)"
| beta: "\<lbrakk>A >>> A'; B >>> B'\<rbrakk> \<Longrightarrow> (App (Fn x T A) B) >>> (A'[x ::= B'])"
| eta:  "A >>> A' \<Longrightarrow> (Fn x T A) >>> (Fn x T A')"
| app:  "\<lbrakk>A >>> A'; B >>> B'; \<not>(\<exists>x T M. A = Fn x T M)\<rbrakk> \<Longrightarrow> (App A B) >>> (App A' B')"

lemma not_fn_prm:
  assumes "\<not>(\<exists>x T M. A = Fn x T M)"
  shows "\<not>(\<exists>x T M. \<pi> \<cdot> A = Fn x T M)"
proof(rule classical)
  assume "\<not>\<not>(\<exists>x T M. \<pi> \<cdot> A = Fn x T M)"
  hence "\<exists>x T M. \<pi> \<cdot> A = Fn x T M" by blast
  hence "\<exists>x T M. (prm_inv \<pi>) \<cdot> (\<pi> \<cdot> A) = (prm_inv \<pi>) \<cdot> Fn x T M" by fastforce
  hence "\<exists>x T M. (prm_inv \<pi> \<diamondop> \<pi>) \<cdot> A = (prm_inv \<pi>) \<cdot> Fn x T M"
    using trm_prm_apply_compose by metis
  hence "\<exists>x T M. A = (prm_inv \<pi>) \<cdot> Fn x T M"
    using prm_inv_compose trm_prm_apply_id by metis
  hence "\<exists>x T M. A = Fn ((prm_inv \<pi>) $ x) T ((prm_inv \<pi>) \<cdot> M)"
    using trm_prm_simp(4) by metis
  hence "\<exists>x T M. A = Fn x T M" by blast
  hence False using assms by blast
  thus ?thesis by blast
qed

lemma complete_development_prm:
  assumes "A >>> A'"
  shows "(\<pi> \<cdot> A) >>> (\<pi> \<cdot> A')"
using assms proof(induction)
  case unit
    thus ?case using complete_development.unit trm_prm_simp(1) by metis
  next
  case (var x)
    thus ?case using complete_development.var trm_prm_simp(2) by metis
  next
  case (beta A A' B B' x T)
    thus ?case using complete_development.beta subst_prm trm_prm_simp(3, 4) by metis
  next
  case (eta A A' x T)
    thus ?case using complete_development.eta trm_prm_simp(4) by metis
  next
  case (app A A' B B')
    thus ?case using complete_development.app trm_prm_simp(3) not_fn_prm by metis
  next
qed

lemma complete_development_fvs:
  assumes "A >>> A'"
  shows "fvs A' \<subseteq> fvs A"
using assms proof(induction)
  case unit
    thus ?case using fvs_simp by auto
  next
  case (var x)
    thus ?case using fvs_simp by auto
  next
  case (beta A A' B B' x T)
    have "fvs (A'[x ::= B']) \<subseteq> fvs A' - {x} \<union> fvs B'" using subst_fvs.
    also have "... \<subseteq> fvs A - {x} \<union> fvs B" using beta.IH by auto
    also have "... \<subseteq> fvs (Fn x T A) \<union> fvs B" using fvs_simp(4) subset_refl by force
    also have "... \<subseteq> fvs (App (Fn x T A) B)" using fvs_simp(3) subset_refl by force
    finally show ?case.
  next
  case (eta A A' x T)
    thus ?case using fvs_simp(4) using Un_Diff subset_Un_eq by (metis (no_types, lifting))
  next
  case (app A A' B B')
    thus ?case using fvs_simp(3) Un_mono by metis
  next
qed

lemma complete_development_fnE:
  assumes "(Fn x T A) >>> X"
  shows "\<exists>A'. (A >>> A') \<and> X = Fn x T A'"
using assms proof(cases, metis unit_not_fn, metis var_not_fn, metis app_not_fn)
  case (eta B B' y S)
    hence "T = S" using trm_simp(4) by metis
    from eta consider "x = y \<and> A = B" | "x \<noteq> y \<and> x \<notin> fvs B \<and> A = [x \<leftrightarrow> y] \<cdot> B"
      using trm_simp(4) by metis
    thus ?thesis proof(cases)
      case 1
        hence "x = y" and "A = B" by auto
        obtain A' where "A' = B'" by auto
        hence "A >>> A'" and "X = Fn x T A'" using eta `A = B` `x = y` `T = S` by auto
        thus ?thesis by auto
      next
      case 2
        hence "x \<noteq> y" "x \<notin> fvs B" and A: "A = [x \<leftrightarrow> y] \<cdot> B" by auto
        hence "x \<notin> fvs B'" using `B >>> B'` complete_development_fvs by auto
        obtain A' where A': "A' = [x \<leftrightarrow> y] \<cdot> B'" by auto
        hence "A >>> A'" using A `B >>> B'` complete_development_prm by auto
        have "X = Fn x T A'"
          using fn_eq `x \<noteq> y` `x \<notin> fvs B'` A' `X = Fn y S B'` `T = S` by metis
        thus ?thesis using `A >>> A'` by auto
      next
    qed
  next
  case (app A A' B B')
    thus ?thesis using app_not_fn by metis
  next
qed

lemma complete_development_exists:
  shows "\<exists>X. (A >>> X)"
proof(induction A rule: trm_induct)
  case 1
    obtain X :: "'a trm" where "X = Unit" by auto
    hence "Unit >>> X" using complete_development.unit by metis
    thus ?case by auto
  next
  case (2 x)
    obtain X where "X = Var x" by auto
    hence "(Var x) >>> X" using complete_development.var by metis
    thus ?case by auto
  next
  case (3 A B)
    from this obtain A' B' where A': "A >>> A'" and B': "B >>> B'" by auto
    consider "(\<exists>x T M. A = Fn x T M)" | "\<not>(\<exists>x T M. A = Fn x T M)" by auto
    thus ?case proof(cases)
      case 1
        from this obtain x T M where A: "A = Fn x T M" by auto
        from this obtain M' where "A' = Fn x T M'" and "M >>> M'"
          using complete_development_fnE A' by metis
        obtain X where "X = (M'[x ::= B'])" by auto
        hence "(App A B) >>> X"
          using complete_development.beta `M >>> M'` B' A by metis
        thus ?thesis by auto
      next
      case 2
        thus ?thesis using complete_development.app A' B' by metis
      next
    qed
  next
  case (4 x T A)
    from this obtain A' where A': "A >>> A'" by auto
    obtain X where "X = Fn x T A'" by auto
    hence "(Fn x T A) >>> X" using complete_development.eta A' by metis
    thus ?case by auto
  next
qed

lemma complete_development_triangle:
  assumes "A >>> D" "A >> B"
  shows "B >> D"
using assms proof(induction arbitrary: B rule: complete_development.induct)
  case unit
    thus ?case using parallel_reduction_unitE parallel_reduction.refl by metis
  next
  case (var x)
    thus ?case using parallel_reduction_varE parallel_reduction.refl by metis
  next
  case (beta A A' C C' x T)
    hence "A >> A'" "C >> C'" using parallel_reduction.refl by metis+
    from `(App (Fn x T A) C) >> B` consider
        "B = App (Fn x T A) C"
      | "B = (A'[x ::= C'])"
      | "B = (App (Fn x T A') C')"
      using parallel_reduction_redexE by metis
    thus ?case proof(cases)
      case 1
        thus ?thesis using parallel_reduction.beta `A >> A'` `C >> C'` by metis
      next
      case 2
        thus ?thesis using parallel_reduction.refl by metis
      next
      case 3
        thus ?thesis using parallel_reduction.beta parallel_reduction.refl by metis
      next
    qed
  next
  case (eta A A' x T B)
    from this consider
      "B = Fn x T A"
    | "(A >> A') \<and> B = Fn x T A'" using parallel_reduction_fnE by metis
    thus ?case proof(cases)
      case 1
        thus ?thesis using eta.IH parallel_reduction.refl parallel_reduction.eta by metis
      next
      case 2
        thus ?thesis using parallel_reduction.refl by metis
      next
    qed
  next
  case (app A A' C C')
    thus ?case using parallel_reduction_nonredexE parallel_reduction.refl by metis
  next
qed

lemma parallel_reduction_diamond:
  assumes "A >> B" "A >> C"
  shows "\<exists>D. (B >> D) \<and> (C >> D)"
proof -
  obtain D where "A >>> D" using complete_development_exists by metis
  hence "(B >> D) \<and> (C >> D)" using complete_development_triangle assms by auto
  thus ?thesis by blast
qed

inductive parallel_reduces :: "'a trm \<Rightarrow> 'a trm \<Rightarrow> bool" ("_ >>\<^sup>* _") where
  reflexive: "A >>\<^sup>* A"
| transitive: "\<lbrakk>A >>\<^sup>* A'; A' >> A''\<rbrakk> \<Longrightarrow> A >>\<^sup>* A''"

lemma parallel_reduces_diamond':
  assumes "A >>\<^sup>* C" "A >> B"
  shows "\<exists>D. (B >>\<^sup>* D) \<and> (C >> D)"
using assms proof(induction)
  case (reflexive A)
    thus ?case using parallel_reduces.reflexive by metis
  next
  case (transitive A A' A'')
    from this obtain C where "B >>\<^sup>* C" "A' >> C" by metis
    from `A' >> C` `A' >> A''` obtain D where "C >> D" "A'' >> D"
      using parallel_reduction_diamond by metis
    thus ?case using parallel_reduces.transitive `B >>\<^sup>* C` by metis
  next
qed

lemma parallel_reduces_diamond:
  assumes "A >>\<^sup>* B" "A >>\<^sup>* C"
  shows "\<exists>D. (B >>\<^sup>* D) \<and> (C >>\<^sup>* D)"
using assms proof(induction)
  case (reflexive A)
    thus ?case using parallel_reduces.reflexive by metis
  next
  case (transitive A A' A'')
    from this obtain C' where "A' >>\<^sup>* C'" "C >>\<^sup>* C'" by metis
    from this obtain D where "A'' >>\<^sup>* D" "C' >> D"
      using `A' >> A''` `A' >>\<^sup>* C'` parallel_reduces_diamond' by metis
    thus ?case using parallel_reduces.transitive `C >>\<^sup>* C'` by metis
  next
qed

lemma beta_reduction_is_parallel_reduction:
  assumes "A \<rightarrow>\<beta> B"
  shows "A >> B"
using assms proof(induction)
  case (beta x T A M)
    thus ?case using parallel_reduction.beta parallel_reduction.refl by metis
  next
  case (app1 A A' B)
    thus ?case using parallel_reduction.app parallel_reduction.refl by metis
  next
  case (app2 A A' B)
    thus ?case using parallel_reduction.app parallel_reduction.refl by metis
  next
  case (fn A A' x T)
    thus ?case using parallel_reduction.eta by metis
  next
qed

lemma parallel_reduction_is_beta_reduction:
  assumes "A >> B"
  shows "A \<rightarrow>\<beta>\<^sup>* B"
using assms proof(induction)
  case (refl A)
    thus ?case using beta_reduces.reflexive.
  next
  case (beta A A' B B' x T)
    hence "(App (Fn x T A) B) \<rightarrow>\<beta>\<^sup>* (App (Fn x T A') B')"
      using `A \<rightarrow>\<beta>\<^sup>* A'`
      beta_reduces_fn beta_reduces_app_left beta_reduces_app_right beta_reduces_composition
      by metis
    moreover have "(App (Fn x T A') B') \<rightarrow>\<beta> (A'[x ::= B'])"
      using beta_reduction.beta.
    ultimately show ?case using beta_reduces.transitive by metis
  next
  case (eta A A' x T)
    thus ?case using beta_reduces_fn by metis
  next
  case (app A A' B B')
    thus ?case using beta_reduces_app_left beta_reduces_app_right beta_reduces_composition by metis
  next
qed

lemma parallel_beta_reduces_equivalent:
  shows "(A >>\<^sup>* B) = (A \<rightarrow>\<beta>\<^sup>* B)"
proof -
  have \<rightarrow>: "(A >>\<^sup>* B) \<Longrightarrow> (A \<rightarrow>\<beta>\<^sup>* B)"
  proof(induction rule: parallel_reduces.induct)
    case (reflexive A)
      thus ?case using beta_reduces.reflexive.
    next
    case (transitive A A' A'')
      thus ?case using beta_reduces_composition parallel_reduction_is_beta_reduction by metis
    next
  qed

  have \<leftarrow>: "(A \<rightarrow>\<beta>\<^sup>* B) \<Longrightarrow> (A >>\<^sup>* B)"
  proof(induction rule: beta_reduces.induct)
    case (reflexive A)
      thus ?case using parallel_reduces.reflexive.
    next
    case (transitive A A' A'')
      thus ?case using parallel_reduces.transitive beta_reduction_is_parallel_reduction by metis
    next
  qed

  from \<leftarrow>\<rightarrow> show "(A >>\<^sup>* B) = (A \<rightarrow>\<beta>\<^sup>* B)" by blast
qed

theorem confluence:
  assumes "A \<rightarrow>\<beta>\<^sup>* B" "A \<rightarrow>\<beta>\<^sup>* C"
  shows "\<exists>D. (B \<rightarrow>\<beta>\<^sup>* D) \<and> (C \<rightarrow>\<beta>\<^sup>* D)"
proof -
  from assms have "A >>\<^sup>* B" "A >>\<^sup>* C" using parallel_beta_reduces_equivalent by metis+
  hence "\<exists>D. (B >>\<^sup>* D) \<and> (C >>\<^sup>* D)" using parallel_reduces_diamond by metis
  thus "\<exists>D. (B \<rightarrow>\<beta>\<^sup>* D) \<and> (C \<rightarrow>\<beta>\<^sup>* D)" using parallel_beta_reduces_equivalent by metis
qed

end
end