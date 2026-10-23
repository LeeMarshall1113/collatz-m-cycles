import Collatz.MCycle109Certs9

/-!
# Certificates of the listed shapes of `data109`, chunks 36..39
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs109_36 : certsOK3 109 20 grid109 grid3_107 data109.certs shapes109_36 = true := by
  decide +kernel

theorem certs109_37 : certsOK3 109 20 grid109 grid3_107 data109.certs shapes109_37 = true := by
  decide +kernel

theorem certs109_38 : certsOK3 109 20 grid109 grid3_107 data109.certs shapes109_38 = true := by
  decide +kernel

theorem certs109_39 : certsOK3 109 20 grid109 grid3_107 data109.certs shapes109_39 = true := by
  decide +kernel

end Collatz
