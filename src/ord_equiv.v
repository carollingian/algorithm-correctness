(* begin hide *)
From Stdlib Require Import Arith.
From Stdlib Require Import Lia.
From Stdlib Require Import List.
(* end hide *)

(** * Introdução *)

(** Equivalência entre diferentes noções de ordenação. *)
(** O objetivo deste arquivo é formalizar e demonstrar a equivalência 
    entre quatro definições distintas de listas ordenadas. *)

(** * Desenvolvimento *)

(** ** Definições de ordenação e propriedades básicas *)

(** *** Ordenação 1 (ord1) *)

(** A primeira definição de ordenação, chamada [ord1], é uma definição 
    indutiva contendo 3 regras de formação:
%\begin{mathpar}
 \inferrule*[Right={$(ord1\_nil)$}]{~}{ord1\ nil} \and \inferrule*[Right={$(ord1\_one)$}]{~}{ord1\ (x::nil)} \and \inferrule*[Right={$(ord1\_all)$}]{x \leq y \and ord1(y::l)}{ord1\ (x::y::l)}
\end{mathpar}%
*)

Inductive ord1 : list nat -> Prop :=
| ord1_nil: ord1 nil
| ord1_one: forall x, ord1 (x::nil)
| ord1_all: forall l x y, x <= y -> ord1 (y::l) -> ord1 (x::y::l).

(** *** Ordenação 2 (ord2) *)

(** A segunda definição de ordenação, chamada [ord2], é uma definição 
    indutiva contendo 2 regras de formação:
%\begin{mathpar}
 \inferrule*[Right={$(ord2\_nil)$}]{~}{ord2\ nil} \and  \inferrule*[Right={$(ord2\_all)$}]{x \leq^* l \and ord2\ l}{ord2\ (x::l)}
\end{mathpar}%
%\noindent% onde $x \leq^* l$ significa que $x$ é menor ou igual que 
todo elemento da lista $l$. Formalmente, este predicado é definido a seguir: *)

Definition le_all x l := forall y, In y l -> x <= y.

(* begin hide *)
Notation "x <=* l" := (le_all x l) (at level 60).  
(* end hide *)

(** printing <=* %\ensuremath{\leq^*}% *)
Inductive ord2 : list nat -> Prop :=
| ord2_nil: ord2 nil
| ord2_all: forall l x, x <=* l -> ord2 l -> ord2 (x::l).
(** printing < %\ensuremath{<}% *)

(** *** Ordenação 3 (ord3) *)

(** A terceira definição de ordenação, chamada [ord3], diz que uma lista 
    está ordenada se cada elemento é menor ou igual ao elemento seguinte: *)

Definition ord3 (l : list nat) : Prop := 
  forall i, length l > 1 -> (S i) < length l -> nth i l 0 <= nth (S i) l 0.

Lemma ord3_nil: ord3 nil.
Proof.
  unfold ord3. intros i H. simpl in H. inversion H.
Qed.

Lemma ord3_one: forall x, ord3 (x::nil).
Proof.
  intro x. unfold ord3. intros i H. simpl in H. lia.
Qed.

Lemma ord3_two: ord3 (1::2::nil).
Proof.
  unfold ord3. intros i H1 H2. simpl in *. destruct i.
  - lia.
  - lia.
Qed.

(** *** Ordenação 4 (ord4) *)

(** A quarta definição de ordenação, chamada [ord4], diz que uma lista 
    está ordenada se cada elemento é menor ou igual que qualquer elemento 
    que esteja em posição anterior: *)

Definition ord4 (l : list nat) : Prop := 
  forall i j, i < j -> j < length l -> nth i l 0 <= nth j l 0.

Lemma ord4_nil: ord4 nil.
Proof. Admitted.

(** ** Lemas auxiliares de equivalência *)

(** *** Lemas para a prova de [ord1_equiv_ord2] *)

(** Para provarmos a equivalência entre as definições indutivas [ord1] e [ord2]
 ([ord1 <-> ord2]), trataremos uma implicância de cada vez. Primeiro [ord1 -> ord2] e,
 em seguida, [ord2 -> ord1]. *)

(** **** Lema  [ord1_to_ord2] *)

(** prova [ord1 -> ord2], ou seja, que toda lista ord1 também é ord2.
  A base utilizada é baseada na divisão de [ord1] em três regras de formação, executada
  pela tática [induction H], que divide a prova em três casos: *)

(** 
  1. Caso [nil]: utilizada a tática apply [ord2_nil], que prova que uma lista vazia pelas 
    regras de [ord1] também é vazia pelas regras de [ord2].
  
  2. Caso de um elemento ([x :: nil]): prova feita com [ord2_all], que exige que
    - [x] seja menor ou igual a todos os elementos do resto da lista ([x <=* nil]). 
      Como a lista [nil] não tem elementos, isso é uma verdade vazia. 
      A tática [inversion Hy] verifica que não faz sentido ter elementos em [nil] e finaliza o problema.
    - o resto da lista esteja ordenado ([ord2 nil]), o que é resolvido com apply [ord2_nil].
  
  3. Caso de dois ou mais elementos ([x :: y :: l]): Sabe-se por hipótese que [x <= y] e 
    que o resto da lista ([y :: l]) está ordenado. Logo, provar [ord2 (x :: y :: l)]. 
    Isso se faz ao provar que [x] é menor ou igual a todos os elementos de [y :: l] ([x <=* y :: l])
    quando se aplica [ord2_all]. Isso é possível com auxílio de um elemento qualquer ([z]) dessa lista.
    Ele pode ser duas coisas e resolvido com [destruct Hz]
    - Ele é o próprio [y]: Se [z] é [y], a hipótese [x <= y] já resolve o problema ([subst. assumption.]).
    - Ele está dentro de [l]: Aqui depende de hipótese de indução ([IHord1]), que garante que [y :: l] já é [ord2]. 
      Usando inversion sobre essa hipótese, [y] é menor que todos os elementos de [l] ([y <= z]). 
      Como [x <= y] e [y <= z], a tática matemática [lia] usa transitividade para concluir que [x <= z].
*)

Lemma ord1_to_ord2 : forall l, ord1 l -> ord2 l.
Proof.
  intros l H. induction H.
  - (* caso nil *)
    apply ord2_nil.
  - (* caso x :: l *)
    apply ord2_all.
    + unfold le_all. intros y Hy. inversion Hy. (* y não pode estar em nil *)
    + apply ord2_nil.
  - (* caso x :: y :: l *)
    apply ord2_all.
    + unfold le_all. intros z Hz. destruct Hz as [Heq | Hin].
      * subst. assumption. (* z é igual a y *)
      * (* z está no resto da lista l *)
        inversion IHord1. subst.
        unfold le_all in H3. apply H3 in Hin. lia.
    + assumption.
Qed.

(** **** Lema  [ord2_to_ord1] *)

(** prova o contrário [ord2 -> ord1]. Como a [ord2] só possui 
duas regras de formação, a indução gera apenas dois casos: *)

(** 
  1. Caso [nil]: Resolvido com [apply ord1_nil].
  
  2. Caso de um ou mais elementos ([x :: l]): Sabe-se que [x <=* l] e que, por hipótese, 
    a lista [l] atende aos critérios da definição de [ord1]. O problema é resolver o 
    fato de [ord1] ter regras diferentes para listas com 1 e listas com 2+ elementos.
    Por isso, a tática [destruct l as [| y l']] analisa dois subcasos da própria lista [l]
    - Se [l] for [nil]: Então a lista original é apenas [x], resolvido com a regra [apply ord1_one].
    - Se [l] tem elementos ([y :: l']): Então a lista original é [x :: y :: l']. 
      A regra que funciona para isso é [ord1_all], que exige que
      - x <= y: Como [x] é menor ou igual a todos os elementos da lista [y :: l'], basta aplicar 
        [apply H] apontando que [y] é o primeiro elemento da lista ([left. reflexivity.]).
      - [y :: l'] está ordenado em [ord1]: a hipótese de indução já assume isso ([assumption.]).
*)

Lemma ord2_to_ord1 : forall l, ord2 l -> ord1 l.
Proof.
  intros l H. induction H.
  - (* caso nil *)
    apply ord1_nil.
  - (* caso x :: l *)
    destruct l as [| y l'].
    + apply ord1_one.
    + apply ord1_all.
      * unfold le_all in H. apply H. simpl. left. reflexivity.
      * assumption.
Qed.

(** *** Lemas para a prova de [ord1_equiv_ord3] *)

(** Para provarmos a equivalência entre as definições indutivas [ord1] e [ord3]
 ([ord1 <-> ord3]), trataremos uma implicância de cada vez. Primeiro [ord1 -> ord3] e,
 em seguida, [ord3 -> ord1]. *)

(** **** Lema  [ord1_to_ord3] *)

(** é baseado em indução sobre a hipótese de ordenação H, porque ord1 é uma definição indutiva.
Por isso, [intros l H. induction H] inicia a prova trazendo a hipótese de que a lista é [ord1]. 
A indução cria três casos exatamente correspondentes às três regras de formação de ord1 *)

(** 
  1. Caso [nil]: A lista está vazia. O lema [ord3_nil] resolve este caso rapidamente.
  
  2. Caso de um elemento ([x :: nil]): A lista possui apenas um elemento. Novamente, 
    o lema auxiliar ord3_one resolve isso direto.
  
  3. Caso de dois ou mais elementos ([x :: y :: l]): Sabemos por hipótese que [x <= y]
    e que o restante da lista está ordenado sob [ord1]. É necessário abrir a definição de [ord3]
    e provar a ordenação para um índice genérico i, que pode ser
    - [i = 0]: É o primeiro elemento da lista. O comando [simpl] resolve as funções [nth], 
      revelando que precisamos provar que [x <= y]. Como essa era a premissa fundamental da regra de [ord1], 
      o comando assumption fecha o subcaso.
    - i > 0: Comparação com elementos mais profundos na lista. 
      O comando [simpl in *] destaca a sublista [y :: l]. [apply IHord1] (a hipótese de indução), 
      garante que a sublista obedece à regra de índices. Os dois comandos 
      [lia] finais apenas confirmam matematicamente que o índice atualizado não estourou o novo tamanho da lista.
*)

Lemma ord1_to_ord3 : forall l, ord1 l -> ord3 l.
Proof.
  intros l H. induction H.
  - (* caso nil *)
    apply ord3_nil.
  - (* caso x :: l *)
    apply ord3_one.
  - (* caso x :: y :: l *)
    unfold ord3 in *. intros i Hlen Hlt.
    destruct i.
    + (* subcaso i = 0, comparando o primeiro elemento com o segundo *)
      simpl. assumption.
    + (* subcaso i > 0, comparando elementos no resto da lista *)
      simpl in *. apply IHord1.
      * (* Prova que o tamanho da sublista é maior que 1 *)
        lia.
      * (* Prova que o índice S i ainda é menor que o tamanho da sublista *)
        lia.
Qed.

(** **** Lema  [ord3_to_ord1] *)

(** é indução sobre a estrutura da lista l, pois [ord3] não é indutivo. Primeiro, ao
iniciar a lista e a indução, divide o problema em [l nill] ou lista [x :: y :: l]. *)

(** 
  1. Caso [nil]: A hipótese diz que ela é ord3. Aplica-se [ord1_nil] direto para fechar o caso.

  2. Caso de um ou mais elementos ([x :: l']): [ord1] trata listas de um elemento de forma diferente 
    de listas com 2 ou mais elementos. Por isso, necessário quebrar o caso em dois subcasos
    - Subcaso de um elemento ([x :: nil]): A lista é exatamente [x]. O comando [apply ord1_one] encerra a prova.
    - Subcaso de dois ou mais elementos ([x :: l'']): necessário aplicar a regra principal [apply ord1_all].
*)

Lemma ord3_to_ord1 : forall l, ord3 l -> ord1 l.
Proof.
  intros l. induction l as [| x l' IH].
  - (* Caso 1: Lista vazia *)
    intro H. apply ord1_nil.
  - (* Caso 2: Lista com elementos *)
    intro H. destruct l' as [| y l''].
    + (* Subcaso: Apenas 1 elemento na lista *)
      apply ord1_one.
    + (* Subcaso: 2 ou mais elementos (x :: y :: l'') *)
      apply ord1_all.
      * (* Precisamos provar que x <= y. O índice 0 no ord3 nos dá isso. *)
        unfold ord3 in H. specialize (H 0).
        simpl in *. apply H; lia.
      * (* Precisamos provar que o resto (y :: l'') é ord1 via Hipótese de Indução *)
        apply IH. unfold ord3 in *. intros i Hlen Hlt.
        specialize (H (S i)). simpl in *. apply H; lia.
Qed.

(** ** Teoremas principais *)

(** O objetivo principal desta proposta é mostrar que as definições 
    [ord1], [ord2], [ord3] e [ord4] são logicamente equivalentes: *)

Theorem ord1_equiv_ord2: forall l, ord1 l <-> ord2 l.
Proof.
  split; intro H.
  - apply ord1_to_ord2; assumption.
  - apply ord2_to_ord1; assumption.
Qed.

Theorem ord1_equiv_ord3: forall l, ord1 l <-> ord3 l.
Proof.
  split; intro H.
  - apply ord1_to_ord3; assumption.
  - apply ord3_to_ord1; assumption.
Qed.

Theorem ord1_equiv_ord4: forall l, ord1 l <-> ord4 l.
Proof.
Admitted.

(** ** Lemas auxiliares para ord4 *)

(** Para provar as equivalências finais envolvendo [ord4], precisamos de 
    duas pontes lógicas, detalhadas a seguir. *)

(** **** Lema [ord4_to_ord3] *)

(** Este lema prova a implicação [ord4 -> ord3]. 
    A lógica fundamenta-se no fato de que [ord3] é apenas um caso particular de [ord4]. 
    Enquanto [ord4] garante que qualquer elemento 
    é menor ou igual a todos os seus sucessores, a [ord3] 
    exige apenas a verificação entre elementos adjacentes (índices [i] e [S i]).
    A prova se desenvolve da seguinte forma:
    - Os comandos [unfold ord3, ord4] expõem as definições.
    - Ao aplicar a hipótese [H] de [ord4], precisamos apenas provar que o índice 
      [i] é estritamente menor que seu sucessor [S i]. *)

Lemma ord4_to_ord3 : forall l, ord4 l -> ord3 l.
Proof.
  intros l H. unfold ord3, ord4 in *.
  intros i Hlen Hlt.
  apply H.
  - lia. (* Prova que i < S i *)
  - assumption.
Qed.

(** **** Lema [ord2_to_ord4] *)

(** Este lema estabelece a implicação [ord2 -> ord4]. 
    A prova é realizada por indução sobre a hipótese de ordenação [ord2] 
    (tática [induction H]), dividindo o problema em dois casos principais:
    
    1. Caso [nil]: Uma lista vazia é trivialmente [ord4]. Como não há elementos, 
       os limites de tamanho da lista invalidam os índices, sendo resolvido com [lia].
       
    2. Caso [x :: l]: A análise depende da posição dos índices [i] e [j]. A tática 
       [destruct i; destruct j] cria subcasos para verificar se estamos acessando 
       o primeiro elemento (índice 0) ou elementos da cauda (índice > 0):
       - Índices impossíveis: Se [i] ou [j] violam [i < j] (ex: 0 < 0), [lia] encerra por absurdo.
       - Acesso cruzado ([i = 0] e [j > 0]): Compara a cabeça [x] com um elemento 
         da cauda. A definição de [ord2] garante que [x] é menor que tudo em [l]. 
         Usamos o lema da biblioteca [nth_In] para associar o acesso por índice 
         à presença do elemento na lista ([In]), satisfazendo a hipótese.
       - Acesso na cauda ([i > 0] e [j > 0]): A comparação ocorre inteiramente dentro 
         da sublista [l]. O caso é resolvido invocando a hipótese de indução ([IHord2]). *)

Lemma ord2_to_ord4 : forall l, ord2 l -> ord4 l.
Proof.
  intros l H. induction H.
  - (* Caso nil: Uma lista vazia*)
    unfold ord4. intros i j Hij Hlen. simpl in Hlen. lia.
  - (* Caso x :: l*)
    unfold ord4 in *. intros i j Hij Hlen.
    destruct i; destruct j.
    + lia. (* 0 < 0*)
    + simpl. apply H. apply nth_In. simpl in Hlen. lia. (* i=0, j>0 *)
    + lia. (* S i < 0*)
    + simpl. apply IHord2; simpl in Hlen; lia. (* ambos > 0, usa hipótese de indução *)
Qed.

(** ** Teoremas Finais de Transitividade *)

(** Os três teoremas finais concluem as equivalências do projeto. 
    Eles não necessitam de novas induções estruturais, pois podem reutilizar 
    as pontes já estabelecidas anteriormente, aplicando a propriedade 
    transitiva das implicações lógicas. *)

(** **** Teorema [ord2_equiv_ord3] *)
(** Demonstra [ord2 <-> ord3]. 
    - A ida faz o caminho lógico [ord2 -> ord1 -> ord3].
    - A volta faz o caminho lógico [ord3 -> ord1 -> ord2]. *)
Theorem ord2_equiv_ord3: forall l, ord2 l <-> ord3 l.
Proof.
  split; intro H.
  - (* Ida (ord2 -> ord3): ord2 -> ord1 -> ord3 *)
    apply ord1_to_ord3. apply ord2_to_ord1. assumption.
  - (* Volta (ord3 -> ord2): ord3 -> ord1 -> ord2 *)
    apply ord1_to_ord2. apply ord3_to_ord1. assumption.
Qed.

(** **** Teorema ord2_equiv_ord4 *)
(** Usamos os lemas auxiliares que acabamos de criar. Para a ida, aplicamos 
    direto o lema [ord2_to_ord4]. Para a volta, fazemos o caminho longo: 
    transformamos ord4 em ord3, depois ord3 em ord1, e finalmente ord1 em ord2. *)
Theorem ord2_equiv_ord4: forall l, ord2 l <-> ord4 l.
Proof.
  split; intro H.
  - (* Ida: ord2 -> ord4 *)
    apply ord2_to_ord4. assumption.
  - (* Volta: ord4 -> ord3 -> ord1 -> ord2 *)
    apply ord1_to_ord2. apply ord3_to_ord1. apply ord4_to_ord3. assumption.
Qed.

(** **** Teorema ord3_equiv_ord4 *)
(** Seguimos a mesma lógica de trânsito entre as provas. Para a ida (ord3 -> ord4), 
    convertemos ord3 para ord1, ord1 para ord2, e usamos o nosso lema [ord2_to_ord4]. 
    A volta é direta com o lema [ord4_to_ord3]. *)
Theorem ord3_equiv_ord4: forall l, ord3 l <-> ord4 l.
Proof.
  split; intro H.
  - (* Ida: ord3 -> ord1 -> ord2 -> ord4 *)
    apply ord2_to_ord4. apply ord1_to_ord2. apply ord3_to_ord1. assumption.
  - (* Volta: ord4 -> ord3 *)
    apply ord4_to_ord3. assumption.
Qed.


(** * Conclusão *)

(** Todas as equivalências propostas entre [ord1], [ord2], [ord3] e [ord4] 
    foram demonstradas, comprovando que as abordagens 
    indutivas e as abordagens baseadas em índices definem de maneira idêntica 
    o conceito de ordenação de listas. *)