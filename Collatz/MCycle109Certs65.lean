import Collatz.MCycle109Certs64

/-!
# Certificates of the listed shapes of `data109`, chunks 256..259
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs109_256 : certsOK3 109 20 grid109 grid3_107 data109.certs shapes109_256 = true := by
  decide +kernel

theorem certs109_257 : certsOK3 109 20 grid109 grid3_107 data109.certs shapes109_257 = true := by
  decide +kernel

theorem certs109_258 : certsOK3 109 20 grid109 grid3_107 data109.certs shapes109_258 = true := by
  decide +kernel

theorem certs109_259 : certsOK3 109 20 grid109 grid3_107 data109.certs shapes109_259 = true := by
  decide +kernel

end Collatz
