<!-- markdownlint-disable MD013 MD052 -->

# BBuf u f+ Sewing Note for the \bar B B u f_+ Sector

This note records the corrected sewing calculation for the sector
\[
(\bar B,B,u,f_+)=(1,2,3,4).
\]
The scan uses `QReplacement -> 2`; the displayed formulas below restore the
physical labels after reduction.

## Sector and Conventions

The heavy pair has spin \(1/2\).  The \(u_\mu\) leg is the massive spin-one leg
at position \(3\), and \(f_+\) is the positive-helicity massless vector at
position \(4\).

\[
\text{leftSpin}=\frac12,\qquad
\text{rightSpins}=\{1,1\},\qquad
\text{rightMass}=\{3\},\qquad
\text{rightPolarization}=\{1,0\}.
\]

The hard relative momentum is
\[
Q=p_1-p_2,
\]
the \(p_-\)-type combination in Eq.~\eqref{eq:momentum_decompose}.  It is
treated as the hard heavy-pair vector in the sewing construction.

The package output also uses reflected square labels.  In the paper-level
display we undo this bookkeeping by
\[
8\mapsto 1,\qquad 7\mapsto 2,\qquad 6\mapsto 3 .
\]

## Chiral Sorting Rule

The scan is organized by
\[
\nu=d_{\rm amp}-n_x,
\]
where \(n_x=1\) only for the static \(x\)-type closed heavy-pair factor and
\(n_x=0\) otherwise.

For this sector:

* `ampDim=3` gives the leading block \(\nu=3\).
* `ampDim=4` gives one \(\nu=3\) \(x\)-type row and two \(\nu=4\) new rows.
* `ampDim=5` and `ampDim=6` are consistency checks; they do not change the
  LO/NLO partition.

The fixed-dimension rank checks are
\[
\operatorname{rank}M_{\rm CF}
\!=\!\operatorname{rank}M_{\rm sew}
\!=\!\operatorname{rank}M_{\rm joined}
\!=\!
\begin{cases}
2,& d_{\rm amp}=3,\\
3,& d_{\rm amp}=4,\\
4,& d_{\rm amp}=5,\\
5,& d_{\rm amp}=6.
\end{cases}
\]

## Leading Order, \(\nu=3\)

There are three leading representatives before flavor projection: two open
rows at `ampDim=3`, plus one static \(x\)-type row at `ampDim=4`.

For `ampDim=3`, use
\[
e^{(3)}_1=\langle23\rangle[14][34],
\qquad
e^{(3)}_2=\langle13\rangle[24][34].
\]

For `ampDim=4`, use
\[
\begin{aligned}
e^{(4)}_1&=\langle34\rangle[14][24][34],
&
e^{(4)}_2&=\langle24\rangle[14][24]^2,
\\
e^{(4)}_3&=\langle13\rangle\langle23\rangle[34]^2 .
\end{aligned}
\]

| row | `ampDim` | \(J_{12}\) | type | \(A_L\) | \(A_R\) | \(A_{\rm sew}\) | reduced representative |
| --- | --- | --- | --- | --- | --- | --- | --- |
| \(L_1\) | \(3\) | \(1\) | open | \(\langle2J\rangle[8J]\) | \(\langle3J\rangle[46][4J]\) | \(-\langle23\rangle[46][48]\) | \(-e^{(3)}_1\) |
| \(L_2\) | \(3\) | \(1\) | open | \(\langle1J\rangle[7J]\) | \(\langle3J\rangle[46][4J]\) | \(-\langle13\rangle[46][47]\) | \(-e^{(3)}_2\) |
| \(L_3\) | \(4\) | \(0\) | \(x\) | \(-\langle12\rangle-[21]\) | \(\langle Q3\rangle[Q4][43]\) | \(-(\langle12\rangle+[21])\langle Q3\rangle[Q4][43]\) | \(-e^{(4)}_1-e^{(4)}_3\) |

The first two rows are the open \(J_{12}=1\) current structures.  The third
row is the static closed \(J_{12}=0\) structure.  Its \(x\)-type factor removes
one hard power, so `ampDim=4` contributes at the same leading chiral order as
the `ampDim=3` open-current rows.

## Next-To-Leading Order, \(\nu=4\)

There are two new next-to-leading representatives before flavor projection.
Both come from `ampDim=4`: the recoil \(y\)-type closed row, and one
independent open \(J_{12}=1\) row.

| row | `ampDim` | \(J_{12}\) | type | \(A_L\) | \(A_R\) | \(A_{\rm sew}\) | reduced representative |
| --- | --- | --- | --- | --- | --- | --- | --- |
| \(N_1\) | \(4\) | \(0\) | \(y\) | \(\langle12\rangle-[21]\) | \(\langle Q3\rangle[Q4][43]\) | \((\langle12\rangle-[21])\langle Q3\rangle[Q4][43]\) | \(-e^{(4)}_1+e^{(4)}_3\) |
| \(N_2\) | \(4\) | \(1\) | open | \([2J][1J]\) | \(\langle Q3\rangle[Q4][4J][3J]\) | \(\langle Q3\rangle[Q4]\bigl([14][23]+[24][13]\bigr)\) | \(-e^{(4)}_1-2e^{(4)}_2\) |

Together with \(L_3\), these two rows span the full `ampDim=4` reduced space:
\[
\operatorname{rank}\{L_3,N_1,N_2\}
\!=\!\operatorname{rank}M_{\rm CF}
\!=\!\operatorname{rank}M_{\rm sew}
\!=\!\operatorname{rank}M_{\rm joined}
\!=3.
\]

## Higher-Dimension Checks

The `ampDim=5` scan gives rank \(4\) and the `ampDim=6` scan gives rank \(5\).
At `ampDim=5` the independent rows are still open \(J_{12}=1\) directions.
At `ampDim=6` the first static \(x\)-type rows appear at \(\nu=5\), so they do
not enter the NLO block.

## Raw Verification Data

The relevant scripts and logs are:

* `Codes/MassiveAmplitude-Code/Test/sewing_bbuf_dims_3_5_note_data.wls`
* `Codes/MassiveAmplitude-Code/logs/sewing_bbuf_dims_3_5_note_data.log`
* `Codes/MassiveAmplitude-Code/Test/sewing_bbuf_chiral_order_note_data.wls`
* `Codes/MassiveAmplitude-Code/logs/sewing_bbuf_chiral_order_note_data.log`
