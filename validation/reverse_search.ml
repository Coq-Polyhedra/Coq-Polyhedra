(*
 * Entrée : A et b, une base admissible I_0 de Ax >= b et une fonction de coût f associée
 * ie I_0 est la base optimale pour f, au sens de Bland
 * 
 * Règle de Bland : étant donné une base I admissible, on calcule le vecteur de coût réduit
 * unique solution du système A_I u = f, et on sélectionne le plus petit indice i \in I tel que u_i < 0
 * On va alors pivoter vers une base J = I - i + j, où j va est le plus petit indice k qui minimise la quantité
 * (A_k x^I - b_k)/(A_k * col i (A_I)^{-1})
 * cf Theory of Linear and Integer Programming (Schrijver), Chapitre 11
 * 
 * Algo d'énumération : récursif sur la base
 * let rec enum I (c^I_kl : 'M(m, n)) (r^I_k : 'cV_m) (g^I : 'cV_n) :=
 *   S := {};
 *   for i \in I do
 *     for j \notin I do
 *       let J = I - i + j in 
 *         if (c^I_ij != 0) && (r^I_j <= 0 || j \in arg max_(k notin I | c^I_ik < 0) (r^I_k / c^I_ik)) 
 *           (* criterion for J to be a feasible basis *) then
 *           S := {(J, c^J, r^J, g^J)} \cup S
 *     done
 *   done;
 *   print S;
 *   S' := filter [fun (J, c^J, r^J, g^J) => I == bland J c^J r^J g^J] S; (* bland should use the c^I and r^I *)
 *   iter enum S' 
 *)
