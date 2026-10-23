import Collatz.MCycle109Certs13

/-!
# Certificates of the listed shapes of `data109`, chunks 52..55
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs109_52 : certsOK3 109 20 grid109 grid3_107 data109.certs shapes109_52 = true := by
  decide +kernel

theorem certs109_53 : certsOK3 109 20 grid109 grid3_107 data109.certs shapes109_53 = true := by
  decide +kernel

theorem certs109_54 : certsOK3 109 20 grid109 grid3_107 data109.certs shapes109_54 = true := by
  decide +kernel

theorem certs109_55 : certsOK3 109 20 grid109 grid3_107 data109.certs shapes109_55 = true := by
  decide +kernel

end Collatz
