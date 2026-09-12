import LeanExe.Extract.Values

open LeanExe.Extract.Core

private def shiftBorrowedRoot : IRStmt :=
  .while (.not (.eqU64 (.local 1) (.u64 0)))
    (.seq (.assign 2 (.local 3))
      (.seq (.assign 3 (.local 0))
        (.assign 1 (.u64Bin .sub (.local 1) (.u64 1)))))

#guard stmtFreshOwnedLocalsAfter #[] [2, 3] shiftBorrowedRoot == []
