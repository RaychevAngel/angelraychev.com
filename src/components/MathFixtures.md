#### Markdown inline and display paths

Inline mathematics must preserve its baseline and script hierarchy: $a_{<t}$,
$x_{i_j}^{n+1}$, $\pi_{\mathrm{rollout}}$, $\mathbb{E}[X \mid Y]$,
$\operatorname{Var}(X)$, and $f'(x)$.

$$
\begin{aligned}
\delta_t &= \log \pi_T(a_t\mid q,c,a_{<t})\\
&\quad -\log \pi_{\mathrm{rollout}}(a_t\mid q,a_{<t}).
\end{aligned}
$$

$$
\begin{cases}
\dfrac{1+\sqrt{x^2+y^2}}{1+\dfrac{1}{n+1}},&x\ge 0,\\[0.5em]
\left\lceil\dfrac{-x}{2}\right\rceil,&x<0.
\end{cases}
$$

| Setting | Expression |
| --- | --- |
| Inline in a table | $M_{\le T}(n,m)=\max_{\lvert V(G)\rvert=n} I_{\le T}(G)$ |
| Delimiters and norms | $\lVert x\rVert_2\le\sqrt{\sum_{i=1}^n x_i^2}$ |
