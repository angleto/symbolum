const cells = document.getElementById('cells');
const line = document.getElementById('line');
const entry = document.getElementById('entry');
const trouble = document.getElementById('trouble');
/*
 * Every element the server marked, in the mode its element says.
 *
 * The selector was `.printed[data-tex]` until 2026-09-18, which was every formula there was: a
 * theorem, set as a block. A rendered `show` page has both, the statement as a block and the
 * sequent of each derivation step inside the line that describes it, so the mode is read off the
 * element rather than fixed here: `.printed` is a block and `.tex` is not. Rendering an inline
 * sequent in display mode puts a line break in the middle of a sentence.
 */
function typeset(){
  if (!window.katex) return;
  for (const el of cells.querySelectorAll('[data-tex]')) {
    const block = el.classList.contains('printed');
    try { katex.render(el.dataset.tex, el, {displayMode:block, throwOnError:false}); }
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
 * replaying a development does. So nothing is refused entry and the wait is shown instead: the form
 * carries `running` while anything is outstanding. What is dropped once accepted, and why, is the
 * paragraph below this one.
 *
 * Which answer wins the rendering stops being a question here rather than being answered. With one
 * request outstanding there is one answer to render, so the page cannot be left showing a state
 * older than the one the server holds.
 */
let queue = Promise.resolve();
let outstanding = 0;
/*
 * Which transcript a submission was written against, as a number rather than as a flag, and what
 * happens to a submission written against an older one.
 *
 * Everything queued behind a conflict was written against a transcript that no longer exists, so
 * sending it would be this file's own defect one step further along. That is still the rule. What
 * it does not cover, and what a flag that never came back down swallowed with it until 2026-09-16,
 * is everything written AFTER the refusal has been rendered: the page has just re-read the
 * transcript the server actually holds, so what is written next is written against what is on the
 * screen. Measured in a browser that day: a conflict was rendered correctly, and the next two
 * commands never reached the server at all while the box emptied as if they had, for the rest of
 * the load, under a message that said to carry on from there.
 *
 * So: a submission carries the epoch it was written in, the epoch moves when the server refuses
 * one, an older epoch is dropped, and a submission written after the refusal was rendered carries
 * the current epoch and goes.
 */
let epoch = 0;
/*
 * What was written and not applied is named in full rather than counted, and goes back into the box
 * where the box can hold it.
 *
 * Losing the text is the half of this that no reload gives back, and the box is emptied by the
 * submit handler before anything is queued, which is what makes typing ahead work and is not worth
 * giving up. So whatever does not land puts it back. Both kinds go in here, because a writer wants
 * the same thing of both: the one the server refused, which is the one most likely to be written
 * again since it is valid against the transcript now on the screen, and the ones behind it that
 * were never sent.
 *
 * `line` is an `<input>`, and an input's value sanitisation strips CR and LF, so two commands put
 * back as one block would arrive silently joined into one unreadable line. The message is therefore
 * where the text always is, and the box gets it back only when what it would get carries no line
 * break and nothing else has been typed into it.
 */
let unapplied = [];
const moved = 'Something else wrote to this session, so the cells above are not the ones this page ' +
  'was writing against. What is above is what the session holds now, and what is written next is ' +
  'written against it and sent.';
function announce(){
  trouble.textContent = unapplied.length === 0 ? moved
    : moved + ' Not applied, each having been written against the transcript that moved: ' +
      unapplied.map(what => '"' + what.replace(/[\r\n]+/g, ' ⏎ ') + '"').join(', ');
}
function settle(){
  entry.classList.remove('running');
  const block = unapplied.join('\n');
  unapplied = [];
  if (block !== '' && !/[\r\n]/.test(block) && line.value === '') line.value = block;
}
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
  const written = epoch;
  outstanding += 1;
  entry.classList.add('running');
  queue = queue.then(async () => {
    /* Only `/run` carries text somebody wrote. A `/truncate` that does not land is a button press
     * against a transcript that has moved, and its body is a cell number: naming it would read as a
     * command and putting it back in the box would put one there. Pressing the button again is the
     * whole of repeating it, and the count to press is on the cells now on the screen. */
    if (written !== epoch) { if (where === '/run') unapplied.push(what); announce(); return; }
    /* Cleared on the way through rather than left standing, because `.trouble` is one element that
     * persists until something overwrites it: a message about a submission that has since been
     * answered reads as a page that is still refusing. */
    if (await post(where, what)) trouble.textContent = '';
    else { epoch += 1; if (where === '/run') unapplied.push(what); announce(); }
  }).catch(error => {
    /* Nothing was rendered, so the page is looking at the same transcript it was looking at before,
     * and what is queued behind is still written against that. Which is why this reports and does
     * not block: if the request did land and the answer was lost, the next one carries a count that
     * is now short by one and the server refuses it, which is the case above and recovers itself. */
    trouble.textContent = 'The session did not answer, so this was not applied: ' + error;
  }).finally(() => {
    outstanding -= 1;
    if (outstanding === 0) settle();
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
/*
 * Going back asks first, and the `confirm` is the one thing on this page an automated caller
 * cannot get past.
 *
 * It is a browser modal: it blocks the page's event loop, and a browser-automation extension
 * driving this tab stops receiving anything at all until a person dismisses it. Measured on
 * 2026-09-18, driving the page through one such extension: loading it, running six commands,
 * reading a refusal and carrying on all worked and screenshotted, and this is the only control
 * that would have stopped that. It is written down rather than replaced, because replacing it is
 * an in-page dialog and that is a decision about the interface: `confirm` is what makes a
 * destructive button honest for the person this tool is for, and that person is the one it was
 * designed for.
 *
 * What it does NOT explain is the block this page was reported with on 2026-09-14, and the
 * difference is worth keeping: that report was a screenshot failing on a freshly loaded page, and
 * nothing here fires without a click. That block did not reproduce on 2026-09-18.
 */
cells.addEventListener('click', e => {
  const button = e.target.closest('.back');
  if (!button) return;
  const count = button.dataset.count;
  const after = document.querySelectorAll('.cell').length - count;
  if (!confirm('Discard ' + after + ' command(s)? Everything after this point goes.')) return;
  send('/truncate', count);
});
window.addEventListener('load', typeset);
