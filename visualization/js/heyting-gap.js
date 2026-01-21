// Dramatic Heyting Gap visualization

const modal = document.getElementById('heyting-gap-modal');

export function showHeytingGapModal(gapResult) {
  modal.classList.remove('hidden');

  // Trigger dramatic entrance animation
  modal.querySelector('.modal-content').style.animation = 'none';
  setTimeout(() => {
    modal.querySelector('.modal-content').style.animation = '';
  }, 10);

  // Add screen shake effect
  document.body.classList.add('shake');
  setTimeout(() => {
    document.body.classList.remove('shake');
  }, 500);
}

export function hideHeytingGapModal() {
  modal.classList.add('hidden');
}
