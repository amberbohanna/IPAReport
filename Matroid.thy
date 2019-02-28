theory Matroid
  imports Main
begin
locale matroid =
  fixes
    E :: "'a set"
  fixes
    \<I> :: "'a set set"
  fixes
    \<B> :: "'a set set"
  assumes
    finite: "finite E"
  assumes
    subset: "\<I> \<subseteq> Pow E"
  assumes
    nonempty: "\<I> \<noteq> {}"
  assumes
    bases_independent: "\<B> \<subseteq> \<I>"
  assumes
    bases_maximal: "B \<in> \<B> \<longrightarrow> (\<forall>e \<in> E - B. (B \<union> {e}) \<notin> \<I>)"
  assumes
    I1: "{} \<subseteq> \<I>"
  assumes
    I2: "(B \<in> \<I>) \<and> (A \<subseteq> B) \<longrightarrow> A \<in> \<I>" 
  assumes
    I3: "\<forall>A \<in> \<I>. \<forall>B \<in> \<I>. card A < card B \<longrightarrow> (\<exists>e \<in> (B - A). A \<union> {e} \<in> \<I>)"
begin
  
lemma bases_equicardinal: 
  fixes X Y:: "'a set"
  assumes A0: "X \<in> \<B>"
  assumes A1: "Y \<in> \<B>"
  assumes contra: "card X < card Y"
  shows "False"
  proof -
    from A0 have 1: "X \<in> \<I>" 
      using bases_independent by(auto)
    from A1 have 2: "Y \<in> \<I>" 
      using bases_independent by(auto)
    from 1 2 contra have 3: "\<exists>e \<in> Y - X. X \<union> {e} \<in> \<I>" 
      using I3 by(auto)
    from 3 have 4: "\<exists>e \<in> E - X. X \<union> {e} \<in> \<I>" 
      using subset by(auto)
    from A0 have 5: "\<forall>e \<in> E - X. X \<union> {e} \<notin> \<I>" 
      using bases_maximal by(auto)
    with 4 have F: "False" by(auto)
    show "False" using F by(auto) 
  qed