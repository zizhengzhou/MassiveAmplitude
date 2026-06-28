VerificationTest[
  (
    SetDirectory[$HBPTestCodeRoot];
    Get[FileNameJoin[{$HBPTestCodeRoot, "Package", "Kernel", "init.m"}]];
    Get[FileNameJoin[{$HBPTestCodeRoot, "SoftHeavyFactorization.executable.m"}]];
    $HBPTestLoaded = True;
    And @@ (
      Length[DownValues[#]] > 0 & /@ {
        ConstructHeavyBaryonPhysicalBasis,
        AuxConstructKinematicFoundation,
        AuxGlobalKinematicReduction,
        AuxDispatchDummyBlocks,
        AuxKroneckerFilteringAndRestore,
        ConstructSU3Tr,
        ConstructIndepCFBlock,
        ConstructLeft3PointOpenBasis,
        ConstructRightResidualSSYT,
        SymmetricSewContract,
        ConstructSewingAmplitudeRecords,
        ConstructIndepSewingBlock,
        CompareSewingToCFBlocks,
        ReduceSt,
        FindIndependentBasisPos
      }
    )
  ),
  True,
  TestID -> "load-old-package-and-soft-heavy-factorization"
]

VerificationTest[
  Sort[Options[ConstructHeavyBaryonPhysicalBasis][[All, 1]]],
  Sort[{mass, su3ShapeList, Verbose, AuditLogDirectory, AuditRunID, AuditVerbose}],
  TestID -> "construct-interface-options"
]
