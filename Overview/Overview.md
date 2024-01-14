::: flushright
# Counterfactual Models
UROP: Miguel Buitrago
Benjamin Brast-McKie
:::

**Overview:** This is a preliminary outline describing the scope of the
project and providing a sense of what motivates the construction. The
primary aim of the project is to use Z3 to evaluate entailments between
counterfactual claims up to some limit in model complexity, providing
countermodels when they exist. By ruling out countermodels up to a
specified level of complexity, we may provide evidence that the
entailment of interest is valid over all models. A second aim is to
provide a method for identifying all entailments up to a specified level
of syntactic complexity that do not admit countermodels below a
specified value for model complexity. The entailments within the
specified value of syntactic complexity may then serve as the basis upon
which to identify a logic for the language. A third and final aim is to
adequately document the project, taking steps towards generalising the
methodology so that a user could investigate the logic for a language by
defining its models and semantic clauses.

A preliminary outline for each part will be provided below and is
subject to change. Settling the details given below constitutes the
first part of the project, though these details may continue to change
throughout.

# Sentence Encoding

The following definitions will use *bitvectors* to encode the
propositional sentences for a language which includes $n$ distinct
sentence letters.

1.  The language is specified by providing a list of operators
    $\mathcal{Q}=\langle Q_1,Q_2,\ldots\rangle$ where each $Q_i$ has a
    finite arity given by $\texttt{Arity}(Q_i)$.

2.  Let $\mathbb{Lit}_n=\lbrace i:1\leq i\leq n\rbrace$ be the first $n$
    *sentence letters* and
    $\mathcal{L}_n=\langle\mathbb{Lit}_n,\mathcal{Q}\rangle$ be a
    propositional language of *rank* $n$ with operators $\mathcal{Q}$.

3.  We may encode the sentences of $\mathcal{L}_n$ in Polish notation as
    follows:

    -   If $A\in\mathbb{Lit}_n$, then $\langle A\rangle$ is a sentence
        of $\mathcal{L}_n$.

    -   If $\texttt{Arity}(Q)=k$ and $B_i$ is a sentence of
        $\mathcal{L}_n$ for each $1\leq i\leq k$, then
        $\langle Q,B_1,\ldots,B_k\rangle$ is a sentence of
        $\mathcal{L}_n$.

4.  It would be convenient have an algorithm for translating sentences
    from standard notation into bitvector notation so that
    $( 1 \vee 2 ) \boxright 3$ can be transformed back and forth with
    $\langle\boxright, \langle\vee, \langle 1\rangle, \langle 2\rangle\rangle, \langle 3\rangle\rangle$.

# Bitvector Frames

This section defines frames with $n$ primitive elements in terms of
*bitvectors* with Boolean values, where the $n$^th^ value of a bitvector
may be interpreted as an *atomic proposition* which is basic way for
things things to be.

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
    $s\circ t\coloneq s.t\in P$.

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

1.  $\langle S,P,\ldbrack\cdot\rdbrack\rangle$ is a *bitvector
    $n$-model* of the propositional language $\mathcal{L}_m$ *iff*
    $\langle S,P\rangle$ is an $n$-frame and
    $\ldbrack p\rdbrack\in\mathbb{P}_{\langle S,P\rangle}$ for every
    sentence letter $p\in\mathbb{Lit}_m$.

2.  We may then define the following operators for $X,Y,V,F\subseteq S$:

    -   $X \otimes Y \coloneq \lbrace s.t : s \in X,\ t \in Y\rbrace$.

    -   $X \oplus Y \coloneq X \cup Y \cup (X \otimes Y)$.

    -   $\neg\langle V,F\rangle \coloneq \langle F,V\rangle$.

    -   $\langle V,F\rangle\wedge\langle V',F'\rangle \coloneq \langle V\otimes V',F\oplus F'\rangle$.

    -   $\langle V,F\rangle\vee\langle V',F'\rangle \coloneq \langle V\oplus V',F\otimes F'\rangle$.

3.  Letting
    $\mathcal{L}_n=\langle\mathbb{Lit}_n,\neg,\wedge,\vee\rangle$ be an
    extensional language, each $n$-model determines a unique proposition
    for the extensional sentences $\varphi$ and $\psi$ of $\mathcal{L}$
    by way of the following semantics:

    -   $\lvert p\rvert=\ldbrack p\rdbrack$ if $p\in\mathbb{Lit}_n$.

    -   $\lvert\langle\neg,\varphi\rangle\rvert=\neg\lvert\varphi\rvert$.

    -   $\lvert\langle\wedge,\varphi,\psi\rangle\rvert=\lvert\varphi\rvert\wedge\lvert\psi\rvert$.

    -   $\lvert\langle\vee,\varphi,\psi\rangle\rvert=\lvert\varphi\rvert\vee\lvert\psi\rvert$.

4.  Given a world state $w$ together with any other state $s$, we may
    consider the set of maximal parts of $w$ which are compatible with
    $s$:\
    $(w)_s\coloneq \lbrace t\sqsubseteq w:t\circ s \wedge \forall r\sqsubseteq w((r\circ s \wedge t \sqsubseteq r) \rightarrow t = r)\rbrace$.

5.  Given a proposition $\langle V,F\rangle$, we may define the set of
    all world states that result from minimally changing $w$ to include
    a state $s\in V$:\
    $\langle V,F\rangle^w\coloneq \lbrace w'\in W:\exists s\in V\exists t\in(w)_s(s.t\sqsubseteq w')\rbrace$.

6.  Given an extensional sentence $\varphi$ and $n$-model
    $\mathcal{M}=\langle S,P,\ldbrack\cdot\rdbrack\rangle$, it will be
    convenient to adopt the notation
    $\lvert\varphi\rvert=\langle\lvert\varphi\rvert^+,\lvert\varphi\rvert^-\rangle$.

7.  Letting
    $\mathcal{L}_n^+=\langle\mathbb{Lit}_n,\neg,\wedge,\vee,\boxright\rangle$
    be a counterfactual language of rank $n$, the extensional sentence
    $\varphi$ and sentences $A$, $B$, and $C$ may be evaluated for truth
    at an $n$-model $\mathcal{M}$ together with a world $w$ as follows:

    -   $\mathcal{M}, w \vDash \varphi$ *iff* there is some
        $s \sqsubseteq w$ where $s \in \lvert\varphi\rvert^+$.

    -   $\mathcal{M}, w \vDash \neg A$ *iff* $\mathcal{M}, w \nvDash A$.

    -   $\mathcal{M}, w \vDash A \wedge B$ *iff*
        $\mathcal{M}, w \vDash A$ and $\mathcal{M}, w \vDash B$.

    -   $\mathcal{M}, w \vDash A \vee B$ *iff* $\mathcal{M}, w \vDash A$
        or $\mathcal{M}, w \vDash B$.

    -   $\mathcal{M}, w \vDash \varphi\boxright C$ *iff*
        $\mathcal{M}, w' \vDash C$ whenever
        $w'\in\lvert\varphi\rvert^w$.

8.  We may read '$\mathcal{M}, w \vDash A$' as '$A$ is true at $w$ in
    $\mathcal{M}$' which, given the definitions above, translates to a
    condition on bitvectors that is either true or false. Thus we may
    ask Z3 if there is an $n$-model $\mathcal{M}$ of $\mathcal{L}_n^+$
    and world $w$ over its corresponding $n$-frame where
    $\mathcal{M}, w \vDash A$.

9.  A world-model pair *satisfies* a set of sentences $\Gamma$ just in
    case every sentence in $\Gamma$ is true in that world on that model.

10. A set of sentences $\Gamma$ is $n$-*satisfiable* just in case there
    is a $n$-model $\mathcal{M}$ and world $w$ that satisfies $\Gamma$,
    and $n$-*unsatisfiable* otherwise.

11. $\Gamma \vDash^n \varphi$ *iff*
    $\Gamma\cup\lbrace\neg\varphi\rbrace$ is $n$-unsatisfiable.

# Logic Search

This section aims to provide a systematic way to find $n$-entailments
without attempting to conduct an exhaustive search over all
$n$-entailments given the size of this space.

# Representations

Organise and print found $n$-entailments as well as graphically
representing countermodels.
