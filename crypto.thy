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

(* y^2 = a*x^3 + b*x + c *)


datatype Kriva = EC nat nat nat Polje

datatype Tacka = T nat nat

fun na_krivi :: "Tacka \<Rightarrow> Kriva \<Rightarrow> bool" where
"na_krivi (T x y) (EC a b c (F p)) \<longleftrightarrow> a*x^3 + b*x + c mod p = y^2 mod p"

fun saberi_EC :: "Tacka \<Rightarrow> Tacka \<Rightarrow> Kriva \<Rightarrow> Tacka" where
"saberi (T x1 y1) (T x2 y2) (EC a b c (F p)) = " (* TODO*) 



end