# Physics Conventions

## Particle Labels

Particles 1 and 2 are the equal-spin heavy pair.  Right-side particles are
labelled 3 through n.

Massive square-spinor labels use the package convention where the conjugate
massive labels are \(2n,2n-1,\ldots,n+1\).  These special labels are only used
for massive square-spinor polarization data.  Momentum labels such as `Q` are
not replaced by massive square labels.

## Mass Convention

Inside the sewing package, massive particles are represented by ordinary
symbols `m1`, `m2`, ..., not by formatted subscript strings.  This avoids
dimension-enumeration artifacts in the legacy CF machinery.

`rightMass -> {3}` means particle 3 is massive.  `rightMass -> {3, 4}` means
particles 3 and 4 are massive.

## Formal Q

The symbolic output may contain formal `Q`.  The default replacement is

```wl
QReplacement -> {1, -2}
```

which means \(Q=p_1-p_2\).  The replacement acts as a momentum-label
replacement inside brackets and does not move bracket slots.

To keep `Q` visible in final symbolic output, use:

```wl
ReplaceQInFinalSymbolForm -> False
```

## Xhard and Xsoft

`Xhard` and `Xsoft` are symbolic left-current factors.  They are preserved in
symbolic output.  Internal reduction converts symbolic output to amp form before
linear-algebra checks, then maps independent results back to symbolic form.

## Symmetric Sewing

The default sewing mode is:

```wl
SewingContractionMode -> "Split"
```

Fully symmetric contractions are expanded into separate terms before
independence selection.  The older summed behavior remains available with:

```wl
SewingContractionMode -> "Sum"
```

## Relative Chiral Order

The current relative chiral-order label is

```wl
ampDim - XhardPower - J
```

where `XhardPower` is read from explicit sewing metadata.  This is a relative
sorting label, not a full physical chiral dimension including external
normalization offsets.

## Identical Particles

`identicalParam` only refers to right-side particles.  Groups containing
particles 1 or 2 are rejected.

Example:

```wl
identicalParam -> {{3, 4}}
```

Identical particles must have compatible spin, mass, polarization scheduling,
and gauge shape information.  The constructor follows the old
`FilterCFBlocksByIdentical` and `ReAssignIdentical` behavior:

* mixed-polarization representatives are kept only once;
* same-polarization representatives are Young-projected.

## SU(3)

SU(3) structure generation calls the legacy color constructor:

```wl
AuxConstructIdenticalColorBasis[su3ShapeList, identicalInfo, IYT]
```

The Lorentz and color structures are combined by direct product, not by ordinary
multiplication.  With color enabled, basis entries carry both
`LorentzSymbolForm` and `SU3Basis`, plus the original `SU3IndexDictionary`.

Common shape labels are:

* `""`: color singlet or no color index.
* `"q"`: fundamental quark-like index.
* `"aq"`: antifundamental index.
* `"g"`: adjoint-like gluon index.
