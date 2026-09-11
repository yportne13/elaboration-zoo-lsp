(function () {
  var input = document.getElementById('search');
  if (!input) return;
  var listing = document.getElementById('listing');
  var results = document.getElementById('results');
  var data = window.TYPORT_SEARCH || [];

  function esc(s) {
    return String(s).replace(/[&<>"]/g, function (c) {
      return { '&': '&amp;', '<': '&lt;', '>': '&gt;', '"': '&quot;' }[c];
    });
  }

  input.addEventListener('input', function () {
    var q = input.value.trim().toLowerCase();
    if (!q) {
      results.innerHTML = '';
      if (listing) listing.style.display = '';
      return;
    }
    if (listing) listing.style.display = 'none';
    var hits = data.filter(function (x) {
      return (
        x.n.toLowerCase().indexOf(q) >= 0 ||
        (x.f || '').toLowerCase().indexOf(q) >= 0 ||
        (x.d || '').toLowerCase().indexOf(q) >= 0
      );
    }).slice(0, 300);
    results.innerHTML =
      '<ul class="items">' +
      hits.map(function (x) {
        return (
          '<li><a href="' + esc(x.u) + '">' + esc(x.n) + '</a> ' +
          '<span class="kind kind-' + esc(x.k) + '">' + esc(x.k) + '</span> ' +
          '<span class="key">' + esc(x.f) + '</span></li>'
        );
      }).join('') +
      '</ul>';
  });
})();
