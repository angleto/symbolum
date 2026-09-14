const cells = document.getElementById('cells');
const line = document.getElementById('line');
function typeset(){
  if (!window.katex) return;
  for (const el of cells.querySelectorAll('.printed[data-tex]')) {
    try { katex.render(el.dataset.tex, el, {displayMode:true, throwOnError:false}); }
    catch (e) { /* leave the source showing, which is what the element already holds */ }
  }
}
async function post(where, what){
  const response = await fetch(where, {method:'POST', body:what});
  cells.innerHTML = await response.text();
  typeset();
  window.scrollTo(0, document.body.scrollHeight);
}
document.getElementById('entry').addEventListener('submit', async e => {
  e.preventDefault();
  const what = line.value.trim();
  if (!what) return;
  line.value = '';
  await post('/run', what);
});
cells.addEventListener('click', async e => {
  const button = e.target.closest('.back');
  if (!button) return;
  const count = button.dataset.count;
  const after = document.querySelectorAll('.cell').length - count;
  if (!confirm('Discard ' + after + ' command(s)? Everything after this point goes.')) return;
  await post('/truncate', count);
});
window.addEventListener('load', typeset);
