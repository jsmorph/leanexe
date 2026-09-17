import { Gpt2 } from "./host.js";
const $ = id => document.getElementById(id);
let runner, stop = false, running = false;
const status = message => { $("status").textContent = message; };
$("stop").onclick = () => { stop = true; status("Stopping after the current token…"); };
$("run").onclick = async () => {
  if (running) return;
  running = true; stop = false; $("run").disabled = true;
  $("status").classList.remove("error");
  try {
    if (!runner) runner = await Gpt2.load(status);
    $("stop").disabled = false;
    const prompt = $("prompt").value, output = $("output");
    output.replaceChildren();
    const echo = document.createElement("span"); echo.className = "prompt-echo"; echo.textContent = prompt; output.append(echo);
    const continuation = document.createTextNode(""); output.append(continuation);
    const decoder = new TextDecoder(), start = performance.now(), initialDispatches = runner.dispatches;
    const result = await runner.generate({ prompt, count: Number($("count").value), temperature: $("temperature").value,
      seed: Number($("seed").value), stopped: () => stop, onProgress: status,
      onBytes: bytes => { continuation.textContent += decoder.decode(bytes, { stream: true }); } });
    continuation.textContent += decoder.decode();
    status(`Finished · ${result.produced} new tokens · ${result.reason}`);
    $("meta").textContent = `${result.promptTokens} prompt tokens · ${result.produced} new tokens · ${((performance.now() - start) / 1000).toFixed(1)} s\n${runner.dispatches - initialDispatches} WGSL dispatches · ${runner.adapterInfo}`;
  } catch (error) { status(error.message); $("status").classList.add("error"); }
  finally { running = false; $("run").disabled = false; $("run").textContent = runner ? "Continue text" : "Load model & continue"; $("stop").disabled = true; }
};
