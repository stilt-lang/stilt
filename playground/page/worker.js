// A worker of the playground: the compiler's, which checks and shows, or, started as
// `worker.js#run`, the interpreter's, which the page stops by ending the worker. It answers each
// request that the page posts, with its `id`, as `engine.js` answers it.

const role = self.location.hash.slice(1);
importScripts(...(role === "run" ? ["interpreter.js"] : ["wasi.js"]), "engine.js");

self.onmessage = async ({ data: { id, request } }) => {
  try {
    self.postMessage({ id, result: await self.StiltEngine.handle(request) });
  } catch (e) {
    self.postMessage({ id, error: String((e && e.message) || e) });
  }
};

self.postMessage({ ready: true });
