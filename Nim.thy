theory Nim
  imports Main
begin

section \<open>Basic bitwise XOR on nat \<close>

fun nat_xor :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "nat_xor 0 y = y"
| "nat_xor x 0 = x"
| "nat_xor x y = ((x mod 2 + y mod 2) mod 2) + 2 * nat_xor (x div 2) (y div 2)"

text \<open>
  Helper lemma: Two natural numbers are equal if and only if 
  their quotients and remainders by 2 are equal.
\<close>

lemma nat_eq_iff_div_mod: "x = y \<longleftrightarrow> x div 2 = y div 2 \<and> x mod 2 = y mod 2" 
  for x y :: nat
  by arith

text \<open>
  We characterize the projection of XOR onto div and mod.
  These are marked [simp] so Isabelle prefers them over expanding the function.
\<close>

lemma nat_xor_mod_2 [simp]: "nat_xor x y mod 2 = (x + y) mod 2"
proof (induction x y rule: nat_xor.induct)
  case (1 y) then show ?case by simp
next
  case (2 x) then show ?case by simp
next
  case (3 x y)
  (* We need mod_add_eq to prove (a mod 2 + b mod 2) mod 2 = (a + b) mod 2 *)
  show ?case by (simp add: mod_add_eq)
qed

lemma nat_xor_zero_right [simp]: "nat_xor x 0 = x"
  by (cases x) simp_all

lemma nat_xor_div_2 [simp]: "nat_xor x y div 2 = nat_xor (x div 2) (y div 2)"
proof (induction x y rule: nat_xor.induct)
  case (1 y) then show ?case by simp
next
  case (2 x) then show ?case by simp
next
  case (3 x y)
  (* (b + 2*rec) div 2 = rec, since b < 2 *)
  show ?case by simp 
qed

text \<open>Now standard properties are trivial consequences of the div/mod behavior.\<close>

lemma nat_xor_comm: "nat_xor x y = nat_xor y x"
proof (induction x y rule: nat_xor.induct)
  case (1 y) 
  then show ?case by simp
next
  case (2 x) 
  then show ?case by simp
next
  case (3 x y)
  (* We check that the Div parts match and the Mod parts match. *)
  show ?case 
    using 3.IH
    by (auto simp add: nat_eq_iff_div_mod add.commute)
qed

lemma nat_xor_assoc: "nat_xor (nat_xor a b) c = nat_xor a (nat_xor b c)"
proof (induction a b arbitrary: c rule: nat_xor.induct)
  case (3 x y)
  show ?case
    (* Proof is now: "Do divs match? Yes (by IH). Do mods match? Yes (associativity)." *)
    using 3.IH 
    by (auto simp add: nat_eq_iff_div_mod mod_add_eq add.assoc)
qed simp_all

lemma nat_xor_zero_left [simp]: "nat_xor 0 x = x"
  by (cases x) simp_all

lemma nat_xor_self [simp]: "nat_xor x x = 0"

proof (induction x rule: less_induct)
  case (less x)
  show ?case
    (* div part is 0 by IH, mod part is (x+x)%2 = 0 *)
    using less.IH 
    by (auto simp add: nat_eq_iff_div_mod)
qed

lemma nat_xor_eq_0_iff [simp]: "(nat_xor x y = 0) \<longleftrightarrow> (x = y)"
proof
  assume "x = y" thus "nat_xor x y = 0" by simp
next
  assume "nat_xor x y = 0"
  thus "x = y"
  proof (induction x y rule: nat_xor.induct)
    case (3 x y)
    (* div matches by IH, mod matches by arithmetic *)
    then show ?case
      using \<open>nat_xor x y = 0\<close>
      by (auto simp add: nat_eq_iff_div_mod split: if_splits)
  qed simp_all
qed

section \<open>Nim sum and positions\<close>

definition nim_sum :: "nat list \<Rightarrow> nat" where
  "nim_sum xs = foldr nat_xor xs 0"

definition winning_position :: "nat list \<Rightarrow> bool" where
  "winning_position piles \<equiv> (nim_sum piles = 0)"

lemma nim_sum_empty [simp]: "nim_sum [] = 0"
  by (simp add: nim_sum_def)

lemma nim_sum_cons [simp]: "nim_sum (x # xs) = nat_xor x (nim_sum xs)"
  by (simp add: nim_sum_def)

lemma foldr_xor_aux: "foldr nat_xor xs a = nat_xor (foldr nat_xor xs 0) a"
proof (induction xs)
  case Nil show ?case by simp
next
  case (Cons x xs)
  show ?case by (simp add: Cons.IH nat_xor_assoc)
qed

lemma nim_sum_append: "nim_sum (xs @ ys) = nat_xor (nim_sum xs) (nim_sum ys)"
  unfolding nim_sum_def by (simp add: foldr_xor_aux)

theorem nim_sum_self_cancel: "nim_sum (xs @ xs) = 0"
  by (simp add: nim_sum_append)

section \<open>Simple position checks\<close>

lemma simple_nim_position:
  assumes "length piles = 1"
  assumes "hd piles > 0"
  shows "\<not> winning_position piles"
proof -
  obtain x where "piles = [x]" using assms(1) by (cases piles; simp)
  with assms(2) have "x > 0" by simp
  then have "nim_sum piles = x" using \<open>piles = [x]\<close> by simp
  then have "nim_sum piles \<noteq> 0" using \<open>x > 0\<close> by simp
  thus ?thesis by (simp add: winning_position_def)
qed

section \<open>Moves and application\<close>

type_synonym move = "nat \<times> nat"

definition is_valid_move :: "nat list \<Rightarrow> move \<Rightarrow> bool" where
  "is_valid_move piles m \<equiv> (case m of (i,n) \<Rightarrow> i < length piles \<and> n < piles ! i)"

definition apply_move :: "nat list \<Rightarrow> move \<Rightarrow> nat list" where
  "apply_move piles m \<equiv> (case m of (i,n) \<Rightarrow> piles[i := n])"

lemma two_pile_nim:
  assumes "piles = [a, b]"
  assumes "a \<noteq> b"
  shows "\<not> winning_position piles"
proof -
  have "nim_sum piles = nat_xor a b" using assms(1) by (simp add: nim_sum_def)
  also have "... \<noteq> 0" using assms(2) by simp (* Uses injectivity lemma *)
  finally show ?thesis by (simp add: winning_position_def)
qed

lemma two_pile_winning_move:
  assumes "piles = [a, b]"
  assumes "a > b"
  shows "is_valid_move piles (0, b)"
  using assms by (simp add: is_valid_move_def)

value "nim_sum [3,4,5]"

end