theory Fresh
imports Main
begin

locale fresh =
  fixes gen_fresh :: "'a set \<Rightarrow> 'a"
  assumes "finite S \<Longrightarrow> gen_fresh S \<notin> S"

definition fresh_nat :: "nat set \<Rightarrow> nat" where
  "fresh_nat S \<equiv> Max S + 1"

interpretation nat: fresh fresh_nat
unfolding fresh_def fresh_nat_def
proof(rule allI, rule impI, rule ccontr)
  fix S :: "nat set" and s :: nat
  assume "finite S" and "\<not> Max S + 1 \<notin> S"
  hence "s \<in> S \<Longrightarrow> s \<le> Max S" by simp
  hence "s \<in> S \<Longrightarrow> s < Max S + 1" by simp
  hence "\<not>(\<exists>s. s \<in> S \<and> s = Max S + 1)"
  by (meson Max_ge `finite S` less_add_one not_le)
  hence "Max S + 1 \<notin> S" by simp
  thus False using `\<not> Max S + 1 \<notin> S` by simp
qed

end