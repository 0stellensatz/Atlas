-- The root all-import module: every source file of the project is reachable from here, and
-- `__check__.py` faults the omission, which a build reports as nothing at all.
--
-- A question day's modules carry French quotes, since `20260813` is not an identifier. Only
-- `Development` is imported: `Challenge.lean` shares its namespace and so cannot enter the
-- same environment, and is built by name instead.

import Atlas.Knowledge.DigitSum
import Atlas.Knowledge.LegendreFormula

import Atlas.Questions.«20260813».Development
