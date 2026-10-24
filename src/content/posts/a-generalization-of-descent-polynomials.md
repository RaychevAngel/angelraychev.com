---
title: "A Generalization of Descent Polynomials"
description: "Polynomiality, sharp multiplicity stabilization and coefficient positivity for prescribed descent sets in multiset permutations."
image: "/assets/descent-polynomials/article-cover.png"
imageAlt: "A generalization of descent polynomials: bounded prefixes reveal polynomiality and sharp multiplicity stabilization in multiset permutations."
updated: 2026-10-24
---

*Sole-author research in enumerative combinatorics. Written in 2021; published in Discrete Mathematics in 2023.*

A permutation records an order. Its **descent set** records exactly where that order falls: the positions at which an entry is larger than the next one. Fix those positions and count all permutations that realize them. Although the permutations become longer as the alphabet grows, their number is eventually governed by a polynomial.

In this paper, I extended that counting problem to **multiset permutations**, where every label appears several times. The resulting family has two parameters: the number of distinct labels and their common multiplicity. I proved polynomiality in the first parameter, found the sharp point at which increasing the second stops changing the answer, and obtained an explicit formula for the stabilized polynomial. Its coefficients have a direct counting interpretation in a particular binomial basis, together with a sharp description of which shifts preserve nonnegativity.

The useful structural idea is that a prescribed descent set leaves only a bounded initial segment free. Everything after the last descent has to be sorted. That converts a count of increasingly long words into a finite collection of order patterns.

## Fixing the positions of the descents

For a word $w=(w_1,\ldots,w_N)$, define

$$
\operatorname{Des}(w)=\{i\in\{1,\ldots,N-1\}:w_i>w_{i+1}\}.
$$

For example,

$$
w=(4,1,3,2)
\quad\Longrightarrow\quad
\operatorname{Des}(w)=\{1,3\}.
$$

The positions are what matter, not the values of the entries at those positions. Equality is not a descent: in a word with repeated letters, $2,2$ is a weakly increasing pair.

The ordinary descent polynomial counts permutations of $\{1,\ldots,n\}$ with one **specified descent set** $I$. This is different from an Eulerian polynomial, which, for a fixed $n$, packages permutations according to their **number** of descents. Here the pattern $I$ stays fixed while $n$ varies.

My generalization replaces the set by the multiset

$$
\{1^m,2^m,\ldots,n^m\},
$$

where the notation means $m$ copies of each label, not exponentiation. Copies of the same label are indistinguishable. If $S_n^{(m)}$ denotes its distinct permutations, the counting function is

$$
\mathfrak d^m(I,n)
=\#\{w\in S_n^{(m)}:\operatorname{Des}(w)=I\}.
$$

Setting $m=1$ recovers the ordinary descent polynomial. The empty descent set always gives $\mathfrak d^m(\varnothing,n)=1$: there is exactly one weakly increasing arrangement.

### A complete example

Take $n=3$, $m=2$ and $I=\{2\}$. We want arrangements of $1,1,2,2,3,3$ with a descent at position $2$ and nowhere else. There are exactly five:

<figure class="result-figure">
  <a href="/research/descent-polynomials/figures/prefix-completion.svg" aria-label="Open the five-arrangement diagram at full size"><img src="/research/descent-polynomials/figures/prefix-completion.svg" alt="The five multiset permutations with descent set {2}: 121233, 131223, 221133, 231123 and 331122. The first two entries determine each word; the remaining four are sorted." loading="lazy" decoding="async" /></a>
  <figcaption>The five arrangements with exactly the required descent pattern. The shaded prefix contains the only choices; each remaining suffix is forced into weakly increasing order.</figcaption>
</figure>

This example already exposes the mechanism behind the general results. Once the first two entries are chosen, the other copies have only one allowable order. We must still check the boundary between the prefix and the suffix: a sorted suffix alone does not guarantee the required final descent.

## Two parameters and two kinds of structure

Let

$$
I=\{\alpha_1<\cdots<\alpha_t\}\ne\varnothing,
\qquad a=\alpha_t.
$$

Let $L$ be the length of the longest consecutive run in $I$. For example, $I=\{2,3,5,7,10,11,12\}$ has $L=3$ because of the run $10,11,12$.

The main results describe different directions in this two-parameter family.

**Polynomiality in the alphabet size.** For every fixed positive multiplicity $m$, the function $\mathfrak d^m(I,n)$ agrees with a polynomial in $n$ for $n\ge a$.

**Stabilization in the multiplicity.** For $n>a$, the counts are weakly increasing as $m$ grows. They stop changing once

$$
m\ge M=a-t+1.
$$

This threshold is sharp when $n\ge L+1$: $M$ is the smallest positive multiplicity from which the count stays constant. If $M=1$, the family is already stable at its first allowed multiplicity. The condition on $n$ matters: a run of $L$ consecutive descents needs $L+1$ distinct labels; with fewer labels, every count is zero.

The two statements should not be conflated. One says how the count changes when more labels become available. The other says that, beyond a precise point, more copies of the same labels add no new possibilities.

### Seeing stabilization in a formula

For the single descent set $I=\{2\}$, the threshold is $M=2$. The two regimes have simple forms:

$$
\begin{aligned}
\mathfrak d^1(\{2\},n)&=\binom n2-1,\\
\mathfrak d^m(\{2\},n)&=\binom{n+1}{2}-1
\qquad(m\ge2).
\end{aligned}
$$

Here $n\ge2$. The first formula chooses two distinct prefix labels; the second allows a repeated label as well. In each case, exactly one prefix fails to produce the boundary descent.

| Distinct labels $n$ | One copy $m=1$ | Two copies $m=2$ | Three copies $m=3$ |
| ---: | ---: | ---: | ---: |
| 2 | 0 | 2 | 2 |
| 3 | 2 | 5 | 5 |
| 4 | 5 | 9 | 9 |
| 5 | 9 | 14 | 14 |
| 6 | 14 | 20 | 20 |

The identical last two columns illustrate a theorem about **all** $m\ge2$, not a conjecture inferred from the displayed cases.

## Why longer words eventually stop adding choices

After position $a=\max I$, no descent is permitted. Consequently, the suffix must be weakly increasing, and the first $a$ entries determine the entire word.

At a descent position, the entry cannot be $1$. There are $t$ such positions, so at most $a-t$ copies of $1$ can occur in the prefix. Once $m\ge a-t+1$, a copy of $1$ is guaranteed to remain for the sorted suffix. Its first entry is therefore $1$.

The last required descent now has the particularly simple condition

$$
w_a>1.
$$

Also, any one label can appear at most $a-t+1$ times in an admissible prefix. To see this, cut the prefix at every weak increase, partitioning it into maximal strictly decreasing runs. Its $t-1$ internal descents leave exactly $a-t+1$ such runs, and a fixed label appears at most once in each. Thus the multiplicity bound no longer excludes any admissible prefix once $m\ge M$.

The stabilized problem is therefore a count of finite words $v=(v_1,\ldots,v_a)$ satisfying

$$
\operatorname{Des}(v)=I\setminus\{a\},
\qquad v_j\in\{1,\ldots,n\},
\qquad v_a>1.
$$

The growing sorted suffix has disappeared from the problem. To prove sharpness, the paper constructs an admissible prefix containing exactly $M$ copies of one label. That prefix cannot exist at multiplicity $M-1$; the assumption $n\ge L+1$ supplies enough labels for its strict drops.

Write $d^\infty(I,n)$ for the resulting stable polynomial. In the polynomial range $n\ge a$, it agrees with $\mathfrak d^m(I,n)$ for every $m\ge M$. The superscript $\infty$ names this finite stabilization; it does not require infinite words or a limiting approximation.

## Two proofs of polynomiality

The paper gives both an elementary counting proof and a symmetric-function proof. They explain the same phenomenon through different representations.

### Count the order patterns in the prefix

Work in the polynomial range $n\ge a$. Temporarily omit the requirement that position $a$ be a descent. Let $D^m(I,n)$ count prefixes of length $a$ with descent set $I\setminus\{a\}$, using each label at most $m$ times.

A prefix uses some number $r\le a$ of distinct labels. Record their multiplicities in increasing label order:

$$
A=(a_1,\ldots,a_r),\qquad
a_1+\cdots+a_r=a,\qquad 1\le a_j\le m.
$$

Let $C(A,I)$ be the number of such prefixes after their labels are normalized to $1,\ldots,r$. Choosing the actual labels contributes $\binom nr$, independently of their order pattern. Hence

$$
D^m(I,n)=
\sum_{A\in\operatorname{Comp}(a,m)}
C(A,I)\binom n{\ell(A)},
$$

where $\operatorname{Comp}(a,m)$ is the finite set of compositions of $a$ with parts at most $m$, and $\ell(A)$ is the number of parts. Every summand is a polynomial in $n$, and all remaining data depend only on $I$ and $m$.

Completing the sorted suffix produces either the desired last descent or no descent at that boundary. Thus

$$
D^m(I,n)=
\mathfrak d^m(I,n)+
\mathfrak d^m(I\setminus\{a\},n).
$$

Induction on the size of the descent set proves polynomiality. The proof turns a global arrangement problem into the choice of labels for finitely many normalized patterns.

### Encode the words as ribbon tableaux

There is also a geometric representation. Break a word at its descents. Each weakly increasing run becomes a row of a ribbon-shaped tableau; strict drops become the strict inequalities in the overlapping columns. A ribbon is a connected skew Young diagram containing no $2\times2$ square.

<figure class="result-figure">
  <a href="/research/descent-polynomials/figures/ribbon-word.svg" aria-label="Open the ribbon-tableau diagram at full size"><img src="/research/descent-polynomials/figures/ribbon-word.svg" alt="The word 1,2,1,2,3,3 is represented by a ribbon with a bottom row containing 1,2 and an upper row containing 1,2,3,3. The overlap places 2 below 1, recording the strict descent at position 2." loading="lazy" decoding="async" /></a>
  <figcaption>The same example as a ribbon tableau. Read the bottom row left to right, then the row above. Weak increases along rows and the strict drop at the shared column encode exactly the word's descent pattern.</figcaption>
</figure>

For the appropriate shape $\lambda/\mu$, the count becomes a coefficient of a skew Schur function:

$$
\mathfrak d^m(I,n)
=[x_1^m\cdots x_n^m]s_{\lambda/\mu}.
$$

The Jacobi–Trudi identity expresses this Schur function as a determinant of complete homogeneous symmetric functions. The determinant's dimension is fixed by $I$. As $n$ grows, only the ribbon's long final row grows; each determinant term has one large factor $h_{nm-u}$ and finitely many factors of fixed total degree $u$.

Extracting the equal-multiplicity coefficient again reduces to choosing labels for a fixed pattern. Each term is eventually polynomial in $n$, so their finite signed sum is too. This proof connects the counting family to symmetric functions, rather than treating the polynomiality as an isolated numerical property.

## An explicit formula for the stable polynomial

In the stable regime, no multiplicity constraint remains in the prefix. Its weakly increasing runs can be counted by stars and bars, and inclusion–exclusion enforces a strict drop at each prescribed internal boundary.

Define the gaps between the descent positions by

$$
\beta_1=\alpha_1,
\qquad \beta_j=\alpha_j-\alpha_{j-1}
\quad(2\le j\le t).
$$

For a composition $A=(a_1,\ldots,a_s)$ of $t$, group consecutive gaps into $s$ blocks; let $\sigma_j$ be the sum of the gaps in the $j$th block. For example, $A=(2,1)$ groups $(\beta_1,\beta_2,\beta_3)$ into $(\beta_1+\beta_2,\beta_3)$.

Put

$$
H_r(n)=\binom{n+r-1}{r}.
$$

This is the number of weakly increasing words of length $r$ on $n$ labels. The paper's formula can then be written compactly as

$$
\boxed{
d^\infty(I,n)=
\sum_{A=(a_1,\ldots,a_s)\in\operatorname{Comp}(t)}
(-1)^{t-s}
\left(\prod_{j=1}^{s-1}H_{\sigma_j}(n)\right)
\bigl(H_{\sigma_s}(n)-1\bigr).
}
$$

Merging adjacent runs removes a required descent, producing the inclusion–exclusion sign. The final subtraction removes the all-$1$ final block, the only weakly increasing block that would end at $1$ rather than above it.

For $I=\{1,3\}$, the gap sequence is $(1,2)$. There are only two compositions of $2$, so

$$
\begin{aligned}
d^\infty(\{1,3\},n)
&=H_1(n)\bigl(H_2(n)-1\bigr)
-\bigl(H_3(n)-1\bigr)\\
&=n\left(\binom{n+1}{2}-1\right)
-\left(\binom{n+2}{3}-1\right)\\
&=\frac{n^3-4n+3}{3}.
\end{aligned}
$$

This is a degree-$3$ polynomial arising from words whose lengths keep growing. The last descent position, rather than the eventual word length, governs that degree.

## Coefficients that count normalized patterns

A polynomial can have positive or negative coefficients depending on its basis. For the stabilized family, the basis

$$
\binom{n-1}{0},\binom{n-1}{1},\binom{n-1}{2},\ldots
$$

has a particularly natural meaning. Write

$$
d^\infty(I,n)=\sum_{i=0}^{a}b_i(I)\binom{n-1}{i}.
$$

The coefficient $b_i(I)$ counts normalized prefixes $v$ of length $a$ such that:

- $\operatorname{Des}(v)=I\setminus\{a\}$;
- all entries lie in $\{1,\ldots,i+1\}$;
- each of $2,\ldots,i+1$ occurs at least once;
- the final entry is greater than $1$.

The label $1$ is optional. The other $i$ labels are mandatory, and choosing their actual values from $\{2,\ldots,n\}$ contributes the factor $\binom{n-1}{i}$. The count therefore separates into a choice of labels and a normalized pattern.

The coefficient theorem is more precise than nonnegativity:

$$
b_i(I)>0\quad\Longleftrightarrow\quad L\le i\le a,
$$

and every other coefficient is zero. In particular, $d^\infty(I,n)$ has degree exactly $a$.

For $I=\{2\}$, the two patterns counted by $b_1$ are $(1,2)$ and $(2,2)$; the one pattern counted by $b_2$ is $(2,3)$. Thus

$$
d^\infty(\{2\},n)
=2\binom{n-1}{1}+\binom{n-1}{2}.
$$

In the unshifted basis, the same polynomial is

$$
d^\infty(\{2\},n)
=-\binom n0+\binom n1+\binom n2.
$$

The negative constant is not a defect in the count. It shows that the choice of basis can reveal or obscure its direct combinatorial structure.

### The shift boundary is sharp

The paper classifies every integer shift. In the expansion in $\bigl(\binom{n+k}{i}\bigr)_{i\ge0}$, all coefficients are integers, and:

- if $k\le-1$, every coefficient is nonnegative;
- if $k\ge0$, at least one coefficient is negative.

For the unshifted basis, write its coefficients as $c_i(I)$. There is an exact initial segment:

$$
c_i(I)=(-1)^{i+t}
\qquad(0\le i\le L).
$$

Pascal's identity transfers nonnegativity toward smaller shifts. Together with the alternating initial coefficients at shift $0$, this identifies $\binom{n-1}{i}$ as the boundary within this family of shifted binomial bases: it retains a direct nonnegative counting interpretation, while every shift to its right introduces a negative coefficient.

## Paper and publication

I carried out most of this work at the Research Science Institute in summer 2021, mentored by Pakawut Jiradilok, who proposed the topic and guided the research. The paper is sole-authored.

**Angel Raychev. “A generalization of descent polynomials.” Discrete Mathematics 346(1), Article 113105, 2023.** [DOI: 10.1016/j.disc.2022.113105](https://doi.org/10.1016/j.disc.2022.113105).

The downloadable paper is the original [September 2021 arXiv preprint](https://arxiv.org/abs/2109.04519), not the publisher's typeset version. It contains the full proofs, seven figures, and references to the descent-polynomial and symmetric-function literature.

The central outcome is a structured family of counting polynomials: an elementary prefix decomposition explains polynomiality, ribbon tableaux place it in the language of symmetric functions, and stabilization exposes coefficients that themselves count finite order patterns.
