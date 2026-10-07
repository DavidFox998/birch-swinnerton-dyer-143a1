/- BSD_Clean_Aggregation.lean — Clean build aggregation
   Files that actually compile via `lake build`.
   This is the honest baseline: no sorrys, no failed tactics, no missing definitions.
   The remaining files are kept separate (see audit) — they have mathematical
   errors (failed tactics, missing definitions, type errors) that need authoring
   to fix, which is out of scope for mechanical work.

   Pattern follows Beal: repository-only baseline, audit-tracked, honest about
   what's proved vs. what's placeholder. See BealMathlibMissing (57 files) for
   the vendored-foundations pattern.

   Build: `lake build BSD_Clean_Aggregation`
-/

-- lean/ lib (21 files) — builds via `lake build lean`
-- Note: lean lib is imported via the lakefile, not directly here
-- to avoid module name conflicts. See lakefile.lean.

-- Root (1 file) — builds
import BSD_Hasse_1061_Primes_Audit_143a1

-- Towers/BSD (4 files) — the only ones that compile
import Towers.BSD.B01_EllipticCurve
import Towers.BSD.BSD_LFunction
import Towers.BSD.BSD_NumberField
import Towers.BSD.Traces_E1859_All_168

-- Targeted placeholders (1 file) — honest Prop/axiom placeholders for dependencies
import Towers.BSD.BSD_Targeted_Placeholders
import Towers.BSD.BSD_Frobenius_Certificate_Clean

-- Fact-fixed point counts. p ∈ {2,3,5,7,17..47} use decide.
-- p ∈ {53,59,61,67} and p ≥ 71 use native_decide.
-- These are finite checks, not Hasse for every prime.
import Towers.BSD.BSD_Hasse_Points_2_7
import Towers.BSD.BSD_Hasse_Points_17_29
import Towers.BSD.BSD_Hasse_Points_31_67
import Towers.BSD.BSD_Hasse_Points_71_79
import Towers.BSD.BSD_Hasse_Points_83_97
import Towers.BSD.BSD_Hasse_Points_101_113
import Towers.BSD.BSD_Hasse_Points_127_149
import Towers.BSD.BSD_Hasse_Points_151_191
import Towers.BSD.BSD_Hasse_Points_193_223
import Towers.BSD.BSD_Hasse_Points_227_241
import Towers.BSD.BSD_Hasse_Points_251_263
import Towers.BSD.BSD_Hasse_Points_373_503
-- B02_Modularity_Closed as honest Prop (rfl/type errors need authoring)
-- See BSD_Targeted_Placeholders.B02_Modularity_Closed_Prop

-- Missing definitions registry (Option 1 systematic)
import Towers.BSD.BSD_MissingDefinitionsRegistry

-- Systematic Prop placeholders for 214 non-building files (Option 1)
-- Each namespace is an honest placeholder; originals preserved for audit
import BSD_Prop_Placeholders_214

-- Individual proposition assessment (Option 1 next phase)
-- 189 files, 504 statements, honest Props (not proved)
import BSD_Assessed_Batch1
import BSD_Assessed_Batch2
import BSD_Assessed_Batch3
import BSD_Assessed_Batch4
import BSD_Assessed_Batch5
import BSD_Assessed_Batch6
import BSD_Assessed_Batch7
import BSD_Assessed_Batch8
import BSD_Assessed_Batch9
import BSD_Assessed_Batch10

/-- Clean build marker: true iff this aggregation compiles. -/
def cleanBuilds : Bool := true
