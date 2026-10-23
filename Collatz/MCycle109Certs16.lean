import Collatz.MCycle109Certs15

/-!
# Certificates of the listed shapes of `data109`, chunks 60..63
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs109_60 : certsOK3 109 20 grid109 grid3_107 data109.certs shapes109_60 = true := by
  decide +kernel

theorem certs109_61 : certsOK3 109 20 grid109 grid3_107 data109.certs shapes109_61 = true := by
  decide +kernel

theorem certs109_62 : certsOK3 109 20 grid109 grid3_107 data109.certs shapes109_62 = true := by
  decide +kernel

theorem certs109_63 : certsOK3 109 20 grid109 grid3_107 data109.certs shapes109_63 = true := by
  decide +kernel

end Collatz
