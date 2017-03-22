theory Fresh
imports Main
begin

class fresh =
  fixes fresh_in :: "'a set \<Rightarrow> 'a"
  assumes "finite S \<Longrightarrow> fresh_in S \<notin> S"

instantiation nat :: fresh
begin
  definition fresh_in_nat :: "nat set \<Rightarrow> nat" where
    [code]: "fresh_in_nat S \<equiv> Max S + 1"

  instance proof
    fix S :: "nat set"
    assume "finite S"
    show "fresh_in S \<notin> S" unfolding fresh_in_nat_def proof
      assume "Max S + 1 \<in> S"
      hence "Max S + 1 \<le> Max S" using `finite S` by auto
      thus False by simp
    qed
  qed
end

end