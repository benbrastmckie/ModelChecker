# Counterfactual Models


**Overview:** This is a preliminary outline describing the scope of the
project, not all of which would have to be completed, but nevertheless
provides a sense of what motivates the construction. A first aim is to
provide a means by which to effectively evaluate entailments between
counterfactual claims up to some limit in model complexity, providing
countermodels when they exist. If an entailment does not have any
countermodels below a specified value of complexity, there is good
reason to belief that the entailment is of interest and is likely to be
valid over the space of all models. A second aim is to provide a method
for identifying all entailments up to a specified level of syntactic
complexity that do not admit countermodels below a specified value for
model complexity. These entailments may then serve as the basis upon
which to identify a logic corresponding to the semantics. A third aim is
to connect a theorem prover in order identify a minimal set of axioms
from which all other valid entailments may be derived.

A preliminary outline for each part will be provided below and is
subject to change. Settling the details given below constitutes the
first part of the project, though these details may continue to change
throughout.

# Bitvector Frames

In order to draw on the power of Z3, a state of the art SMT solver, this
section will define frames of complexity $n$ in terms of *bitvectors*
which are included as a primitive type in Z3.

1.  A $n$-*state* $s=\langle s_1,\ldots,s_n\rangle$ is any sequence of
    1s and 0s of length $n$.

2.  An $n$-state $s$ is *part of* an $n$-state $t$ (i.e.,
    $s\sqsubseteq t$) *iff* $s_i\leq t_i$ for all $1\leq i\leq n$.

3.  Letting $X$ be a set of $n$-states and
    $\texttt{Max}_i(X)=\texttt{Max}(\lbrace s_i:s\in X\rbrace)$ be the
    maximum of the $i$^th^ entries, the *fusion*
    $\bigsqcup X=\langle\texttt{Max}_1(X),\ldots,\texttt{Max}_n(X)\rangle$
    includes the maximum entry for each of the states in $X$. We may
    represent the fusion $\bigsqcup\lbrace s,t,\ldots\rbrace=s.t.\ldots$
    for ease of exposition.

4.  A set of $n$-states $S$ forms a *state space iff* $\bigsqcup X\in S$
    for all $X\subseteq S$.

5.  $\langle S,P\rangle$ is a *modal $n$-frame iff* $S$ is a state space
    and $P\subseteq S$ is a nonempty set of *possible states* where
    $s\in P$ whenever $s\sqsubseteq t$ for some $t\in P$.

6.  $s$ and $t$ are *compatible iff* their fusion is possible, i.e.,
    $s\circ = s.t\in P$.

7.  $w$ is a *world state* over the $n$-frame $\langle S,P\rangle$ *iff*
    $w$ is possible and every state $t$ that is compatible with $w$ is
    part of $w$. Thus each $n$-frame determines a set of world states
    $W=\lbrace w\in P: s\sqsubseteq w \text{ whenever } s\circ w\rbrace$.

8.  $V,F\subseteq S$ are *exhaustive* over the $n$-frame
    $\langle S,P\rangle$ *iff* every $s\in P$ is compatible with a state
    $t$ in either $V$ or $F$.

9.  $V,F\subseteq S$ are *exclusive* over the $n$-frame
    $\langle S,P\rangle$ *iff* the states in $V$ are incompatible with
    the states in $F$.

10. $X$ is closed over a state space $S$ *iff* $\bigsqcup Y\in X$
    whenever $Y\subseteq X$.

11. $\langle V,F\rangle$ is a *proposition* over the $n$-frame
    $\langle S,P\rangle$ *iff* $V,F\subseteq S$ are closed, exhaustive,
    and exclusive. Let $\mathbb{P}_{\langle S,P\rangle}$ be the
    propositions over $\langle S,P\rangle$.

# Counterfactual Semantics

This section defines $n$-models in terms of $n$-frames, providing the
semantics for a propositional language with a counterfactual conditional
operator.

1.  Letting $\mathbb{L}=\lbrace p_i:i\in\mathbb{N}\rbrace$ be the set
    of sentence letters, $\langle S,P,\lvert\cdot\rvert\rangle$ is a
    *bitvector $n$-model* *iff* $\langle S,P\rangle$ is an $n$-frame and
    $\lvert\cdot\rvert:\mathcal{L}\to\mathbb{P}_{\langle S,P\rangle}$ is
    a function mapping the sentence letters in $\mathbb{L}$ to
    propositions in $\mathbb{P}_{\langle S,P\rangle}$.

2.  We may then define the following operators:

    -   $X \otimes Y = \lbrace s.t : s \in X,\ t \in Y\rbrace$.

    -   $X \oplus Y = X \cup Y \cup (X \otimes Y)$.

    -   $\neg\langle V,F\rangle = \langle F,V\rangle$.

    -   $\langle V,F\rangle\wedge\langle V',F'\rangle = \langle V\otimes V',F\oplus F'\rangle$.

    -   $\langle V,F\rangle\vee\langle V',F'\rangle = \langle V\oplus V',F\otimes F'\rangle$.

3.  Letting $\mathcal{L}=\langle\mathbb{L},\neg,\wedge,\vee\rangle$ be
    an extensional language, every $n$-model over an $n$-frame
    determines a unique proposition for the extensional sentences
    $\varphi$ and $\psi$ of $\mathcal{L}$ by way of the following
    semantics:

    -   $\lvert\neg\varphi\rvert=\neg\lvert\varphi\rvert$.

    -   $\lvert\varphi\wedge\psi\rvert=\lvert\varphi\rvert\wedge\lvert\psi\rvert$.

    -   $\lvert\varphi\vee\psi\rvert=\lvert\varphi\rvert\vee\lvert\psi\rvert$.

4.  Given a world state $w$ together with any other state $s$, we may
    consider the set of maximal parts of $w$ which are compatible with
    $s$:\
    = \lbrace t\sqsubseteq w:t\circ s \wedge \forall r\sqsubseteq w((r\circ s \wedge t \sqsubseteq r) \rightarrow t = r)\rbrace$.

5.  Given a proposition $\langle V,F\rangle$, we may define the set of
    all world states that result from minimally changing $w$ to include
    a state $s\in V$:\
    $\langle = \lbrace w'\in W:\exists s\in V\exists t\in(w)_s(s.t\sqsubseteq w')\rbrace$.

6.  Letting
    $\mathcal{L}^+=\langle\mathcal{L},\neg,\wedge,\vee,\Rightarrow\rangle$
    be a counterfactual language, sentences $A$, $B$, and $C$ may be
    evaluated for truth at an $n$-model $\mathcal{M}$ together with a
    world $w$ where we assume the notation
    $\lvert\varphi\rvert=\langle\lvert\varphi\rvert^+,\lvert\varphi\rvert^-\rangle$:

    -   $\mathcal{M}, w \vDash \varphi$ *iff* there is some
        $s \sqsubseteq w$ where $s \in \lvert\varphi\rvert^+$.

    -   $\mathcal{M}, w \vDash \neg A$ *iff* $\mathcal{M}, w \nvDash A$.

    -   $\mathcal{M}, w \vDash A \wedge B$ *iff*
        $\mathcal{M}, w \vDash A$ and $\mathcal{M}, w \vDash B$.

    -   $\mathcal{M}, w \vDash A \vee B$ *iff* $\mathcal{M}, w \vDash A$
        or $\mathcal{M}, w \vDash B$.

    -   $\mathcal{M}, w \vDash \varphi\Rightarrow C$ *iff*
        $\mathcal{M}, w' \vDash C$ whenever
        $w'\in\lvert\varphi\rvert^w$.

    We may read '$\mathcal{M}, w \vDash A$' as '$A$ is true in $w$ on
    $\mathcal{M}$'.

7.  A world-model pair *satisfies* a set of sentences $\Gamma$ just in
    case every sentence in $\Gamma$ is true in that world on that model.

8.  A set of sentences $\Gamma$ is $n$-*satisfiable* just in case there
    is a $n$-model $\mathcal{M}$ and world $w$ that satisfies $\Gamma$,
    and $n$-*unsatisfiable* otherwise.

9.  $\Gamma \vDash^n \varphi$ *iff*
    $\Gamma\cup\lbrace\neg\varphi\rbrace$ is $n$-unsatisfiable.

# Model Checker

This section aims to deploy Z3 to check sets of sentences for
$n$-unsatisfiability.

1.  Choose a theorem prover to decide sentence encoding.

2.  Sentences are constructed in two stages. (1) Extensional sentences
    are constructed from the sentence letters $\mathbb{L}$ together
    with the extensional operators $\neg,\wedge,$ and $\vee$. (2)
    Counterfactual sentences are constructed from the extensional
    sentences together with $\neg,\wedge,\vee,$ and $\Rightarrow$.

3.  Sentence complexity is measured by the number of operators and sets
    of sentences are measured by the sum of the complexity of its
    members.

4.  Given a set of $r$ sentences $\Gamma$ and model order $n$, use Z3 to
    evaluate whether $\Gamma$ is $n$-satisfiable, storing all models
    that satisfy $\Gamma$ by updating a global file `rank-r` to record
    findings.

    -   Let `rank-r` be a file which begins empty and is updated to
        include entries for the sets of $r$ sentences that have been
        checked so far where entries are ordered according to their
        complexity.

    -   Entries in `rank-r` should include: (1) a set of $r$ sentences
        $\Gamma$; (2) a model order number $n$ with a default value of
        0; and (3) a table of countermodels organised by order if any.

    -   Before checking whether a set of $r$ sentences $\Gamma$ is
        $n$-satisfiable, check to see if an entry exists in `rank-r`. If
        there is an entry for $\Gamma$ with order number $m\geq n$, then
        return 'unsatisfiable' and halt. If there is an entry for
        $\Gamma$ with order number $m < n$, then check for satisfiable
        models of order $k$ for $m\leq k\leq n$. If there is no entry
        for $\Gamma$, then proceed to check whether $\Gamma$ is
        $n$-unsatisfiable.

5.  If $\mathcal{M}$ is an $n$-model that has been found to satisfy the
    set of $r$ sentences $\Gamma$, store $\mathcal{M}$ in a new entry in
    `rank-r` if an entry for $\Gamma$ does not already exist, and
    otherwise add $\mathcal{M}$ to the entry in `rank-r` for $\Gamma$.

6.  If $\Gamma$ is found to be $n$-unsatisfiable, create an entry for
    $\Gamma$ in `rank-r` if none exists and store $n$ alongside
    $\Gamma$. If there is an entry for $\Gamma$ in `rank-r`, replace the
    stored model order number $m$ with $n$ if $n > m$.

# Ordered Sentences

TODO: continue revisions

1.  Let
    $\mathcal{L}_i=\lbrace p_j:j\in\mathbb{N}\text{ and } j\leq i\rbrace$
    be the set of the first $i$ sentence letters.

2.  Let $\mathbb{O}=\lbrace\neg,\wedge,\vee,\Rightarrow\rbrace$ be the set
    of primitive operators.

3.  The well-formed sentences of a language with counterfactual and
    extensional operators do not permit counterfactual operators to
    occur in the antecedent of a counterfactual sentence. In order to
    devise versatile conventions it will be important to look at the
    syntax used in Prover9 or similar theorem provers.

4.  A sentence has rank $r$ just in case it only includes sentence
    letters in $\mathcal{L}_r$. We may begin by restricting
    consideration to sentences with low rank, e.g., $r\leq5$ since rank
    will amplify the number of models.

5.  Second to rank, sentences can be ordered according to how many
    sentential operators they include, referring to this number as their
    complexity $c$. Rank should take president over complexity, though
    it is also important to restrict consideration to low complexity,
    e.g., $c\leq5$.

6.  Beginning with rank $r=1$, sentences will need to be generated and
    stored in the order of their complexity before moving to rank $r=2$.

7.  Each sentence should have a hash.

8.  Beginning with $r=1$, the hash for each sentence should be stored in
    a list for $r=1$, ordered by complexity. We will need a separate
    $r$-list for each value $r\leq 5$ so that we may easily extend these
    lists to include higher complexity sentences. New lists for $r>5$
    may be added later.

9.  Each hash in an $r$-list should be stored with a bypass parameter
    that can be turned on or off so that sentences that are later deemed
    to be uninteresting can be skipped without removing them from the
    list.

10. Given a rank $r$, complexity $c$, and multiplicity $m$, populate and
    store all sets of at most $m$ hash codes for sentences with rank
    $k\leq r$ and complexity $l\leq c$ in a $(r,c,m)$-list which can be
    incrementally extended.

11. Each set of hash codes $\Gamma$ should be stored alongside a
    verifier list and a falsifier list that can later be populated with
    the hash codes for models which satisfy $\Gamma$ or which do not
    satisfy $\Gamma$, respectively.

# Representations

Organise and print findings provided by the model checker as well as
means of graphically representing models for satisfiable sets of
interest.
