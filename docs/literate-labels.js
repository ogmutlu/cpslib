// Use the declaration's anchor, rather than references or parameter names in its code.
for (const doc of document.querySelectorAll('.code-content > .mod-doc:not([id])')) {
    const code = doc.nextElementSibling;
    if (!code?.classList.contains('code-box')) continue;
    const name = code.querySelector('[data-binding^="const-"][id]');
    if (!name) continue;
    const label = document.createElement('div');
    label.className = 'definition-label';
    const identifier = document.createElement('code');
    identifier.textContent = name.textContent.trim();
    label.append('Definition: ', identifier);
    doc.prepend(label);
    doc.dataset.definitionName = identifier.textContent;
}
