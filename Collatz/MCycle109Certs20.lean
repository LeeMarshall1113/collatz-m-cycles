import Collatz.MCycle109Certs19

/-!
# Certificates of the listed shapes of `data109`, chunks 76..79
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs109_76 : certsOK3 109 20 grid109 grid3_107 data109.certs shapes109_76 = true := by
  decide +kernel

theorem certs109_77 : certsOK3 109 20 grid109 grid3_107 data109.certs shapes109_77 = true := by
  decide +kernel

theorem certs109_78 : certsOK3 109 20 grid109 grid3_107 data109.certs shapes109_78 = true := by
  decide +kernel

theorem certs109_79 : certsOK3 109 20 grid109 grid3_107 data109.certs shapes109_79 = true := by
  decide +kernel

end Collatz
