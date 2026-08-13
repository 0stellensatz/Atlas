-- The root all-import module: every source file of the project is reachable from here, and
-- `__check__.py` faults the omission, which a build reports as nothing at all.
--
-- A question day's modules carry French quotes, since `20260813` is not an identifier. Only
-- `Development` is imported: `Challenge.lean` shares its namespace and so cannot enter the
-- same environment, and is built by name instead.

import Atlas.Knowledge.AbsoluteDegree
import Atlas.Knowledge.AbsoluteInertiaDegree
import Atlas.Knowledge.AbsoluteRamificationIndex
import Atlas.Knowledge.ClosedDerivedSeries
import Atlas.Knowledge.DigitSum
import Atlas.Knowledge.FilteredIso
import Atlas.Knowledge.FilteredProfiniteGroup
import Atlas.Knowledge.HigherUnitGroup
import Atlas.Knowledge.IsJumpPair
import Atlas.Knowledge.IsJumpSet
import Atlas.Knowledge.IsMStepSolvable
import Atlas.Knowledge.IsMixedCharLocalField
import Atlas.Knowledge.JumpMultiplicity
import Atlas.Knowledge.JumpOrder
import Atlas.Knowledge.JumpPairOf
import Atlas.Knowledge.JumpSetEquiv
import Atlas.Knowledge.JumpSetExtremal
import Atlas.Knowledge.JumpSetInduction
import Atlas.Knowledge.JumpSetOf
import Atlas.Knowledge.JumpSetSmall
import Atlas.Knowledge.LegendreFormula
import Atlas.Knowledge.MStepSolvableExtension
import Atlas.Knowledge.MStepSolvableQuotient
import Atlas.Knowledge.OutFilt
import Atlas.Knowledge.ParityIndex
import Atlas.Knowledge.ResidueCharacteristic
import Atlas.Knowledge.RootOfUnityExponent
import Atlas.Knowledge.Shift
import Atlas.Knowledge.ShiftEPrime
import Atlas.Knowledge.ShiftEStar
import Atlas.Knowledge.ShiftRhoEP
import Atlas.Knowledge.ShiftRhoP
import Atlas.Knowledge.ShiftT
import Atlas.Knowledge.ShiftTStar
import Atlas.Knowledge.TRhoEP

import Atlas.Questions.«20260813».Development
