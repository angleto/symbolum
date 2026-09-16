const cells = document.getElementById('cells');
const line = document.getElementById('line');
const entry = document.getElementById('entry');
const trouble = document.getElementById('trouble');
function typeset(){
  if (!window.katex) return;
  for (const el of cells.querySelectorAll('.printed[data-tex]')) {
    try { katex.render(el.dataset.tex, el, {displayMode:true, throwOnError:false}); }
    catch (e) { /* leave the source showing, which is what the element already holds */ }
  }
}
/*
 * One request at a time, chained, and the transcript this page is looking at named on each one.
 *
 * Both halves matter and neither is the other's fix. Until 2026-09-16 the submit handler fired a
 * `fetch` and waited for nothing, so five commands written faster than the round trip were five
 * POSTs racing each other: the server numbered them in the order they arrived, and a `derive`
 * landed before the `assume` it cites and failed naming a fact that did not exist yet. The queue
 * is what puts them back in the order they were written in. The header is what says which
 * transcript they were written against, so the server can refuse a command written against a
 * transcript that has since moved instead of applying it anyway.
 *
 * A queue and not a disabled box, which was the other design. Disabling is visible and throws away
 * what is typed or pasted while a request is in flight, and typing ahead is exactly what somebody
 * replaying a development does. So nothing is dropped and the wait is shown instead: the form
 * carries `running` while anything is outstanding.
 *
 * Which answer wins the rendering stops being a question here rather than being answered. With one
 * request outstanding there is one answer to render, so the page cannot be left showing a state
 * older than the one the server holds.
 */
let queue = Promise.resolve();
let outstanding = 0;
let stalled = false;
async function post(where, what){
  const response = await fetch(where, {
    method: 'POST',
    headers: {'Symbolum-After': String(cells.querySelectorAll('.cell').length)},
    body: what
  });
  cells.innerHTML = await response.text();
  typeset();
  window.scrollTo(0, document.body.scrollHeight);
  return response.ok;
}
function send(where, what){
  outstanding += 1;
  entry.classList.add('running');
  queue = queue.then(async () => {
    /* Everything queued behind a conflict was written against a transcript that no longer exists,
     * so sending it would be this file's own defect one step further along. */
    if (stalled) return;
    if (!await post(where, what)) {
      stalled = true;
      trouble.textContent = 'Something else wrote to this session, so the cells above are not the ' +
        'ones this page was writing against, and nothing that was still queued was sent. What is ' +
        'above is what the session holds now: carry on from there.';
    }
  }).catch(error => {
    stalled = true;
    trouble.textContent = 'The session did not answer, so nothing further was sent: ' + error;
  }).finally(() => {
    outstanding -= 1;
    if (outstanding === 0) entry.classList.remove('running');
  });
  return queue;
}
entry.addEventListener('submit', e => {
  e.preventDefault();
  const what = line.value.trim();
  if (!what) return;
  line.value = '';
  send('/run', what);
});
/*
 * A paste carrying more than one line is one submission of many commands, not many submissions.
 *
 * Pasting a development is the obvious way to replay one, and it is the case that made the race
 * easy to meet, since a person pasting outruns the network exactly as automation does. Sent whole,
 * the lines are folded over one state by the server in the order they appear, so the network gets
 * no vote on their order at all.
 *
 * What is submitted is the value the box would have held: what is before the caret, the paste, and
 * what is after it. Anything else silently drops a line somebody had started typing.
 */
line.addEventListener('paste', e => {
  const pasted = (e.clipboardData || window.clipboardData).getData('text');
  if (!/[\r\n]/.test(pasted)) return;
  e.preventDefault();
  const whole = line.value.slice(0, line.selectionStart) + pasted + line.value.slice(line.selectionEnd);
  line.value = '';
  send('/run', whole);
});
cells.addEventListener('click', e => {
  const button = e.target.closest('.back');
  if (!button) return;
  const count = button.dataset.count;
  const after = document.querySelectorAll('.cell').length - count;
  if (!confirm('Discard ' + after + ' command(s)? Everything after this point goes.')) return;
  send('/truncate', count);
});
window.addEventListener('load', typeset);
