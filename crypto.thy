theory crypto
  imports Complex_Main
begin

datatype Polje = F nat

primrec elementi :: "Polje \<Rightarrow> nat set" where
"elementi (F x) = {0..x-1}"

primrec saberi :: "nat \<Rightarrow> nat \<Rightarrow> Polje \<Rightarrow> nat" where 
"saberi x y (F p) = (if {x,y} \<subset> elementi (F p) then (x + y) mod p else 1000)"

primrec pomnozi :: "nat \<Rightarrow> nat \<Rightarrow> Polje \<Rightarrow> nat" where 
"pomnozi x y (F p) = (if {x,y} \<subset> elementi (F p) then (x * y) mod p else 1000)"

(* ne radi... *)
fun eea :: "nat \<Rightarrow> nat \<Rightarrow> (nat \<times> nat \<times> nat) " where 
"eea 0 b = (b, 0 , 1) " |
"eea a b = (let (g,  y,  x) = eea (b mod a) a
 in (g, x - (b div a) * y, y))"

value "eea 15 18"

(* 
def eea(a, b):
	
	returns a tuple (x,y,z)
	where gcd(a,b) = x = y*a + z*b
	
	if a == 0:
		return (b, 0, 1)
	else:
		g, y, x = eea(b % a, a)
		return (g, x - (b // a) * y, y)

*)

(* y^2 = x^3 + a*x + b *)


datatype Kriva = EC nat nat Polje

datatype Tacka = T nat nat | TACKA_INF

fun na_krivi :: "Tacka \<Rightarrow> Kriva \<Rightarrow> bool" where
"na_krivi (T x y) (EC a b (F p)) \<longleftrightarrow> (x^3 + a*x + b) mod p = y^2 mod p" | 
"na_krivi TACKA_INF (EC a b (F p)) \<longleftrightarrow> True"

(* pretpostavimo da je drugi argument prost pa uvek postoji inverz *)
fun inverse :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
 "inverse x y =  (x^(y-2)) mod y"
 

fun inverse_ef :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
"inverse_ef a m = (let	(g, x, y) = eea a m 
in x mod m)"

value "inverse 2 7"
value "inverse 2 13"

fun oduzmi_mod :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
"oduzmi_mod x y p = (if x \<ge> y then (x-y) mod p else (p-((y-x) mod p)) mod p)"

value "oduzmi_mod 13 27 4"
value "oduzmi_mod 3 13 5"
value "oduzmi_mod 26 27 3"

fun saberi_EC :: "Tacka \<Rightarrow> Tacka \<Rightarrow> Kriva \<Rightarrow> Tacka" where
"saberi_EC TACKA_INF X K = X" |
"saberi_EC X TACKA_INF K = X" |

(* dupliranje - potrebno function i dokaz zaustavljanja*)
(*
"saberi_EC (T x y) (T x y) (EC a b c (F p)) =
(let s = (3 * x*x + a) mod p * inverse ((2 * y) mod p) p
in let x' = oduzmi_mod (s*s) (2 * x) p
in let y' = oduzmi_mod (s * oduzmi_mod x x' p) y p
in ( T x' y'))" |
*)


"saberi_EC (T x1 y1) (T x2 y2) (EC a b (F p)) = 
(let s = oduzmi_mod y2 y1 p * (inverse (oduzmi_mod x2 x1 p) p)
in let x = oduzmi_mod (oduzmi_mod (s*s) x1 p) x2 p
in let y = oduzmi_mod ( s * (oduzmi_mod x1 x p)) y1 p
in (T x y)
)"

(*
  apply auto
  apply (metis Kriva.exhaust Polje.exhaust Tacka.exhaust)
*)

value "na_krivi (T 3 1) (EC 2 2 (F 17))"
value "na_krivi (T 6 3) (EC 2 2 (F 17))"
value "saberi_EC (T 3 1) (T 6 3) (EC 2 2 (F 17))"
value "na_krivi (saberi_EC (T 3 1) (T 6 3) (EC 2 2 (F 17))) (EC 2 2 (F 17))"

  
(* X, Y \<in> EC \<longrightarrow> X + Y \<in> EC *)
lemma saberi_zat:
  assumes "na_krivi X K"
  assumes "na_krivi Y K"
  shows "na_krivi (saberi_EC X Y K) K"
  sorry
 

(* X + Y = Y + X *)
lemma saberi_kom:
  "saberi_EC X Y K = saberi_EC Y X K"
  sorry

(* (X + Y) + Z =  X + (Y + Z) *)
lemma saberi_asoc:
  "saberi_EC (saberi_EC X Y K) Z K = saberi_EC X (saberi_EC Y Z K) K"
  sorry


primrec pomnozi_EC :: "nat \<Rightarrow> Tacka \<Rightarrow> Kriva \<Rightarrow> Tacka" where
"pomnozi_EC 0 X K = TACKA_INF" |
"pomnozi_EC (Suc n) X K = saberi_EC X (pomnozi_EC n X K) K"

lemma pom_na_krivi:
  assumes "na_krivi X K"
  fixes n::nat
  shows "na_krivi (pomnozi_EC n X K) K"
  sorry


end