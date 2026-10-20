;;; vui-epub.el ---                                  -*- lexical-binding: t; -*-

;; Copyright (C) 2026  Qiqi Jin

;; Author: Qiqi Jin <ginqi7@gmail.com>
;; Keywords:

;; This program is free software; you can redistribute it and/or modify
;; it under the terms of the GNU General Public License as published by
;; the Free Software Foundation, either version 3 of the License, or
;; (at your option) any later version.

;; This program is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;; GNU General Public License for more details.

;; You should have received a copy of the GNU General Public License
;; along with this program.  If not, see <https://www.gnu.org/licenses/>.

;;; Commentary:

;;

;;; Code:

(require 'vui-html)
(require 'cl-lib)
(require 'dom)
(require 'esxml-query)
(require 'image)
(require 'seq)
(require 'shr)
(require 'url-parse)
(require 'url-util)

(require 'bookmark)
(require 'imenu)
(require 'org)
(require 'recentf)

;;; EPUB preparation

(defgroup vui-epub nil
  "EPUB reader mode"
  :group 'multimedia)

(defcustom vui-epub-unzip-program (executable-find "unzip")
  "Path to decompression executable."
  :type '(file :must-match t)
  :group 'vui-epub)

(defcustom vui-epub-unzip-args '("-od" directory filename)
  "Arguments to decompression executable.
This variable expects a list of strings, except for `directory'
and `filename' symbols, which will be replaced accordingly when
opening an EPUB file."
  :type '(repeat (choice (string :tag "Argument")
                         (const :tag "Directory" directory)
                         (const :tag "Filename" filename)))
  :group 'vui-epub)

(defcustom vui-epub-render-html-function 'vui-epub-render-html
  "Function used to render HTML.
It's called without arguments with a buffer containing HTML and
should change it to contain the rendered version of it."
  :type 'function
  :group 'vui-epub)

(defcustom vui-epub-pre-html-render-hook nil
  "Hook run before `vui-epub-render-html'."
  :type 'hook
  :group 'vui-epub)

(defcustom vui-epub-post-html-render-hook nil
  "Hook run after `vui-epub-render-html'."
  :type 'hook
  :group 'vui-epub)

(defcustom vui-epub-save-place-file (locate-user-emacs-file "vui-epub-places")
  "File name where last reading places are saved to and restored from.
If set to `nil', no saving and restoring is performed."
  :type '(choice (file  :tag "File name")
                 (const :tag "Don't save last reading places" nil))
  :group 'vui-epub)

(defvar-local vui-epub-file-name nil
  "Path to the EPUB file backing this buffer.")

(defvar-local vui-epub-initialize-work-dir-p t
  "Set to nil if no working directory should be initialized.")
(put 'vui-epub-initialize-work-dir-p 'permanent-local t)

(defvar-local vui-epub-remove-work-dir-on-exit-p t
  "Set to nil if working directory should be preserved after exit.")
(put 'vui-epub-remove-work-dir-on-exit-p 'permanent-local t)

(defvar-local vui-epub-work-dir nil
  "Directory containing the buffer's EPUB files.")
(put 'vui-epub-work-dir 'permanent-local t)

(defvar-local vui-epub-content-file nil
  "Path to the EPUB buffer's .opf file.")

(defvar-local vui-epub-epub-version nil
  "Version string of the EPUB buffer.")

(defvar-local vui-epub-metadata nil
  "Metadata of the EPUB buffer.")

(defvar-local vui-epub-documents nil
  "Alist for the EPUB buffer's documents.
Each alist item consists of the identifier and full path.")

(defvar-local vui-epub-documents-index 0
  "Index of the currently rendered document in the EPUB buffer.")

(defvar-local vui-epub-toc-id nil
  "TOC identifier of the EPUB buffer.")

(defvar-local vui-epub-source-buffer nil
  "Buffer holding the EPUB state for the rendered HTML buffer.
`vui-html-mount' renders into `vui-html-buffer-name', so link
callbacks run outside the EPUB buffer.  This variable lets them
get back to the buffer that owns the EPUB state.")

(defvar-local vui-epub-history nil
  "Stack of documents user has visited.
Each element of the stack is a list (NODEINDEX BUFFERPOS).")

(defvar-local vui-epub-history-forward nil
  "Stack of documents user has visited with `vui-epub-history-back' command.
Each element of the stack is a list (NODEINDEX BUFFERPOS).")

(defun vui-epub-make-path (directory file)
  "Create a path from DIRECTORY and FILE."
  (concat (file-name-as-directory directory) file))

(defun vui-epub-directory-files (directory)
  "Returns a list of files in DIRECTORY except for . and .."
  (seq-remove (lambda (file) (string-match-p "/\\.\\(?:\\.\\)?\\'" file))
              (directory-files directory t)))

(defun vui-epub-contains-nested-directory-p (directory)
  "Non-nil if DIRECTORY contains exactly one directory."
  (let* ((files (vui-epub-directory-files directory))
         (file (car files)))
    (and (= (length files) 1)
         (file-directory-p file)
         file)))

(defun vui-epub-unnest-directory (directory child)
  "Move contents of CHILD into DIRECTORY, then delete CHILD."
  ;; FIXME: this will most certainly fail for con/con
  (dolist (item (vui-epub-directory-files child))
    (rename-file item directory))
  (delete-directory child))

(defun vui-epub--fix-permissions (file-or-directory mode)
  (let* ((modes (file-modes file-or-directory))
         (fixed-mode (file-modes-symbolic-to-number mode modes)))
    (set-file-modes file-or-directory fixed-mode)))

(defun vui-epub-fix-permissions (directory)
  "Iterate recursively through DIRECTORY to fix its files."
  (vui-epub--fix-permissions directory "+rx")
  (dolist (file (vui-epub-directory-files directory))
    (if (file-directory-p file)
        (vui-epub-fix-permissions file)
      (vui-epub--fix-permissions file "+r"))))

(defun vui-epub-unzip-epub (directory filename)
  "Extract FILENAME into DIRECTORY.
Unnecessary nesting is removed with `vui-epub-unnest-directory'."
  (let* ((status (apply #'call-process vui-epub-unzip-program nil "*vui-epub unzip*" t
                        (mapcar (lambda (arg)
                                  (cond
                                   ((eq arg 'directory) directory)
                                   ((eq arg 'filename) filename)
                                   (t arg)))
                                vui-epub-unzip-args)))
         child)
    (while (setq child (vui-epub-contains-nested-directory-p directory))
      (vui-epub-unnest-directory directory child))
    ;; HACK: unzip preserves file permissions, no matter how silly they
    ;; are, so ensure files and directories are readable
    (vui-epub-fix-permissions directory)
    status))

(defun vui-epub-warn (message &optional level)
  "Like `display-warning', but for vui-epub-specific warnings.
Displays MESSAGE in a warnings buffer, with LEVEL as severity."
  (display-warning 'vui-epub message level))

(defmacro vui-epub-ignore-file-errors (&rest body)
  "Like `ignore-errors', but for file errors."
  `(condition-case nil (progn ,@body) (file-error nil)))

(defun vui-epub-slurp (filename &optional parse-xml-p)
  "Return the contents of FILENAME.
If PARSE-XML-P is t, return the contents as parsed by libxml."
  (with-temp-buffer
    (insert-file-contents filename)
    (if parse-xml-p
        (libxml-parse-xml-region (point-min) (point-max))
      (buffer-string))))

(defun vui-epub-mimetype-valid-p (directory)
  "Return t if DIRECTORY contains a valid EPUB mimetype file."
  (vui-epub-ignore-file-errors
    (let ((filename (vui-epub-make-path directory "mimetype")))
      (equal (vui-epub-slurp filename) "application/epub+zip"))))

(defun vui-epub-container-filename (directory)
  "Return the container filename for DIRECTORY."
  (let ((filename (vui-epub-make-path directory "META-INF")))
    (vui-epub-make-path filename "container.xml")))

(defun vui-epub-container-content-filename (content)
  "Return the content filename for CONTENT."
  (let* ((query "container>rootfiles>rootfile[media-type='application/oebps-package+xml']")
         (node (esxml-query query content)))
    (dom-attr node 'full-path)))

(defun vui-epub-container-valid-p (directory)
  "Return t if DIRECTORY holds a valid EPUB container."
  (let ((filename (vui-epub-container-filename directory)))
    (when (and filename (file-exists-p filename))
      (let* ((content (vui-epub-slurp filename t))
             (content-file (vui-epub-container-content-filename content)))
        (when (and content content-file)
          (file-exists-p (vui-epub-make-path directory content-file)))))))

(defun vui-epub-epub-valid-p (directory)
  "Return t if DIRECTORY makes up a valid EPUB document."
  (when (not (vui-epub-mimetype-valid-p directory))
    (message "Invalid mimetype"))
  (vui-epub-container-valid-p directory))

(defun vui-epub-urldecode (string)
  "Return urldecoded version of STRING or nil."
  (when string
    (url-unhex-string string)))

(defun vui-epub-content-version (content)
  "Return the EPUB version for CONTENT."
  (let* ((node (esxml-query "package" content))
         (version (dom-attr node 'version)))
    (when (not version)
      (error "Version not specified"))
    version))

(defun vui-epub-content-unique-identifier-name (content)
  "Return the unique identifier name referenced in CONTENT.
This is used in `vui-epub-content-unique-identifier' to retrieve the
the specific type of unique identifier."
  (let* ((node (esxml-query "package[unique-identifier]" content))
         (name (dom-attr node 'unique-identifier)))
    (when (not name)
      (error "Unique identifier name not specified"))
    name))

(defun vui-epub-content-unique-identifier (content)
  "Return the the unique identifier for CONTENT."
  (let* ((name (vui-epub-content-unique-identifier-name content))
         (selector (format "package>metadata>identifier[id='%s']"
                           (esxml-query-css-escape name)))
         (id (car (dom-children (esxml-query selector content)))))
    (when (not id)
      (error "Unique identifier not found by its name: %s" name))
    (intern id)))

;; NOTE: unique identifier is queried separately as identifiers can
;; appear more than once and only one of them can be the unique one
(defvar vui-epub-required-metadata-tags '(title language)
  "Required metadata tags used for `vui-epub-content-metadata'.")

(defvar vui-epub-optional-metadata-tags
  '(contributor coverage creator date description format
    publisher relation rights source subject type)
  "Optional metadata tags used for `vui-epub-content-metadata'.")

(defun vui-epub-content-metadata (content)
  "Return a metadata alist for CONTENT.
Required keys are \\='identifier and everything in
`vui-epub-required-metadata-tags', optional keys are in
`vui-epub-optional-metadata-tags'."
  (let* ((identifier (vui-epub-content-unique-identifier content))
         (candidates (mapcar (lambda (node)
                               (cons (dom-tag node) (car (dom-children node))))
                             (esxml-query-all "package>metadata>*" content)))
         (required (mapcar (lambda (tag)
                             (let ((candidate (cdr (assq tag candidates))))
                               (when (not candidate)
                                 ;; NOTE: this should ideally be a
                                 ;; warning, but `warn' is too obtrusive
                                 (message "Required metadatum %s not found" tag))
                               (cons tag candidate)))
                           vui-epub-required-metadata-tags))
         (optional (mapcar (lambda (tag) (cons tag (cdr (assq tag candidates))))
                           vui-epub-optional-metadata-tags)))
    (append `((identifier . ,identifier)) required optional)))

(defun vui-epub-content-manifest (directory content)
  "Extract an alist of manifest files for CONTENT in DIRECTORY.
Each alist item consists of the identifier and full path."
  (mapcar (lambda (node)
            (let ((id (dom-attr node 'id))
                  (href (dom-attr node 'href)))
              (cons (intern id)
                    (vui-epub-make-path directory (vui-epub-urldecode href)))))
          (esxml-query-all "package>manifest>item" content)))

(defun vui-epub-content-spine (content)
  "Extract a list of spine identifiers for CONTENT."
  (mapcar (lambda (node) (intern (dom-attr node 'idref)))
          (esxml-query-all "package>spine>itemref" content)))

(defun vui-epub--content-epub2-files (content manifest files)
  (let* ((node (esxml-query "package>spine[toc]" content))
         (id (dom-attr node 'toc)))
    (when (not id)
      (error "EPUB 2 NCX ID not found"))
    (setq vui-epub-toc-id (intern id))
    (let ((toc-file (assq vui-epub-toc-id manifest)))
      (when (not toc-file)
        (error "EPUB 2 NCX file not found"))
      (cons toc-file files))))

(defun vui-epub--content-epub3-files (content manifest files)
  (let* ((node (esxml-query "package>manifest>item[properties~=nav]" content))
         (id (dom-attr node 'id)))
    (when (not id)
      (error "EPUB 3 <nav> ID not found"))
    (setq vui-epub-toc-id (intern id))
    (let ((toc-file (assq vui-epub-toc-id manifest)))
      (when (not toc-file)
        (error "EPUB 3 <nav> file not found"))
      (setq files (seq-remove (lambda (item) (eq (car item) vui-epub-toc-id)) files))
      (cons toc-file files))))

(defun vui-epub-content-files (directory content)
  "Create correctly ordered file alist for CONTENT in DIRECTORY.
Each alist item consists of the identifier and full path."
  (let* ((manifest (vui-epub-content-manifest directory content))
         (spine (vui-epub-content-spine content))
         (files (mapcar (lambda (item) (assq item manifest)) spine)))
    (if (version< vui-epub-epub-version "3.0")
        (vui-epub--content-epub2-files content manifest files)
      (vui-epub--content-epub3-files content manifest files))))

(defun vui-epub--walk-ncx-node (node)
  (let ((tag (dom-tag node))
        (children (seq-filter (lambda (child) (eq (dom-tag child) 'navPoint))
                              (dom-children node))))
    (cond
     ((eq tag 'navMap)
      (insert "<ol>\n")
      (mapc (lambda (node) (vui-epub--walk-ncx-node node)) children)
      (insert "</ol>\n"))
     ((eq tag 'navPoint)
      (let* ((navlabel-node (dom-by-tag node 'navLabel))
             (label-node (dom-by-tag navlabel-node 'text))
             (content-node (dom-by-tag node 'content))
             (href (vui-epub-urldecode (dom-attr content-node 'src)))
             (label (and label-node (car (dom-children label-node)))))
        (when (not href)
          (error "Navigation point is missing href attribute"))
        (let ((link (format "<a href=\"%s\">%s</a>"
                            (url-insert-entities-in-string href)
                            (url-insert-entities-in-string (or label href)))))
          (if children
              (progn
                (insert (format "<li>\n%s\n<ol>\n" link))
                (mapc (lambda (node) (vui-epub--walk-ncx-node node))
                      children)
                (insert (format "</ol>\n</li>\n")))
            (insert (format "<li>\n%s\n</li>\n" link)))))))))

(defun vui-epub-ncx-to-html (path)
  "Convert NCX document at PATH to HTML."
  (let ((root (esxml-query "navMap" (vui-epub-slurp path t))))
    (with-temp-buffer
      (vui-epub--walk-ncx-node root)
      (buffer-string))))

;;; UI

(defun vui-epub-clean-up ()
  "Delete temporary files of the current EPUB buffer."
  (when (and vui-epub-remove-work-dir-on-exit-p vui-epub-work-dir)
    (let ((identifier (cdr (assq 'identifier vui-epub-metadata)))
          (index (if (integerp vui-epub-documents-index)
                     vui-epub-documents-index
                   0)))
      (vui-epub-save-place identifier index (point)))
    (vui-epub-ignore-file-errors
     (delete-directory vui-epub-work-dir t))))

(defun vui-epub-clean-up-all ()
  "Delete temporary files of all opened EPUB buffers."
  (dolist (buffer (buffer-list))
    (with-current-buffer buffer
      (when (eq major-mode 'vui-epub-mode)
        (vui-epub-clean-up)))))

(defun vui-epub-external-url-p (url)
  "Return t if URL refers to an external document."
  (and (url-type (url-generic-parse-url url)) t))

(defun vui-epub-url-filename-and-target (url)
  "Return a list of URL's filename and target."
  (setq url (url-generic-parse-url url))
  (mapcar 'vui-epub-urldecode (list (url-filename url) (url-target url))))

;; adapted from `shr-rescale-image'
;; TODO: adjust to latest shr code (which added zooming support)
;; TODO: support width/height as supplied in img/image/svg attributes
(defun vui-epub-insert-image (path alt)
  "Insert an image for PATH at point, falling back to ALT.
This function honors `shr-max-image-proportion' if possible."
  (let ((type (if (or (and (fboundp 'image-transforms-p) (image-transforms-p))
                      (not (fboundp 'imagemagick-types)))
                  nil
                'imagemagick)))
    (if (not (display-graphic-p))
        (insert alt)
      (seq-let (x1 y1 x2 y2) (window-inside-pixel-edges
                              (get-buffer-window (current-buffer)))
        (let ((image
               ;; `create-image' errors out for unsupported image types
               (ignore-errors
                 (create-image path type nil
                               :ascent 100
                               :max-width (truncate (* shr-max-image-proportion
                                                       (- x2 x1)))
                               :max-height (truncate (* shr-max-image-proportion
                                                        (- y2 y1)))))))
          (if image
              (insert-image image)
            (insert alt)))))))

(defun vui-epub-render-html ()
  "Render HTML in the current EPUB buffer with vui-html."
  (run-hooks 'vui-epub-pre-html-render-hook)
  (let ((vui-html-browse-url #'vui-epub-browse-url)
        ;; Render in place so link callbacks and EPUB commands see the
        ;; buffer-local state (`vui-epub-documents', `vui-epub-toc-id',
        ;; ...).  `vui-epub-mode' derives from `vui-mode', so
        ;; `vui-mount' will not replace the major mode.
        (vui-html-buffer-name (buffer-name))
        (html (buffer-string)))
    (vui-html-mount html)
    ;; Link callbacks look this up when a link is clicked, long after
    ;; the `let' above is gone, so bind it buffer-locally as well.
    (setq-local vui-html-browse-url #'vui-epub-browse-url)
    (setq-local vui-epub-source-buffer (current-buffer)))
  (run-hooks 'vui-epub-post-html-render-hook))

(defun vui-epub--keep-unmodified (&rest _)
  "Clear the buffer's modified flag after it changes.
The buffer holds a rendered view of the EPUB rather than the
archive's contents, so it should never be considered modified."
  (set-buffer-modified-p nil))

(defun vui-epub--after-rerender (instance)
  "Clear the modified flag after vui re-renders INSTANCE's buffer.
Re-renders run with `inhibit-modification-hooks', so
`after-change-functions' cannot keep the flag clear."
  (let ((buffer (vui-instance-buffer instance)))
    (when (buffer-live-p buffer)
      (with-current-buffer buffer
        (when (derived-mode-p 'vui-epub-mode)
          (set-buffer-modified-p nil))))))

(defun vui-epub--confirm-kill ()
  "Allow killing the buffer without asking whether to save it.
The buffer is a view of the EPUB, not a file that can be saved, so
a lingering modified flag should not get in the way."
  (set-buffer-modified-p nil)
  t)

(unless (advice-member-p #'vui-epub--after-rerender 'vui--rerender-buffer)
  (advice-add 'vui--rerender-buffer :after #'vui-epub--after-rerender))

(defun vui-epub-render-document ()
  "Render the document referenced by `vui-epub-documents-index'.
If the document path refers to an image (as determined by
`image-type-file-name-regexps'), an image is inserted, otherwise
the HTML is rendered with `vui-epub-render-html-function'."
  (interactive)
  (seq-let (id &rest path) (aref vui-epub-documents vui-epub-documents-index)
    (let (;; HACK: this should be looked up in the manifest
          (imagep (seq-find (lambda (item) (string-match-p (car item) path))
                            image-type-file-name-regexps))
          ;; NOTE: allows resolving image references correctly
          (default-directory (file-name-directory path))
          ;; `widget-before-change' (installed by `vui-mount') signals
          ;; when text changes outside a field unless this is non-nil.
          (inhibit-read-only t)
          buffer-read-only)
      (erase-buffer)

      (cond
       (imagep
        (vui-epub-insert-image path ""))
       ((and (version< vui-epub-epub-version "3.0")
             (eq id vui-epub-toc-id))
        (insert (vui-epub-ncx-to-html path)))
       (t
        (insert (vui-epub-slurp path))))

      (when (not imagep)
        (funcall vui-epub-render-html-function))
      ;; NOTE: this is how doc-view avoids overwriting the file
      (set-buffer-modified-p nil)
      (goto-char (point-min)))))

(defun vui-epub-find-document (predicate)
  "Return first item in `vui-epub-documents' PREDICATE is true for."
  (let ((i 0)
        done)
    (while (and (not done)
                (< i (length vui-epub-documents)))
      (when (funcall predicate (aref vui-epub-documents i))
        (setq done t))
      (setq i (1+ i)))
    (when done
      (1- i))))

(defun vui-epub-goto-document (index)
  "Go to the document denoted by INDEX."
  (let ((history (cons (list vui-epub-documents-index (point))
                       vui-epub-history)))
    (setq vui-epub-documents-index index)
    (vui-epub-render-document)
    (setq vui-epub-history history)))

(defun vui-epub-goto-toc ()
  "Go to the TOC index and render the TOC document."
  (interactive)
  (let ((index (vui-epub-find-document (lambda (doc) (eq (car doc) vui-epub-toc-id)))))
    (when (not index)
      (error "Couldn't locate TOC"))
    (vui-epub-goto-document index)))

(defun vui-epub-view-source ()
  "View the source of the current document in a new buffer."
  (interactive)
  (find-file (cdr (aref vui-epub-documents vui-epub-documents-index))))

(defun vui-epub-view-content-source ()
  "View the source of the content file in a new buffer."
  (interactive)
  (find-file vui-epub-content-file))

(defun vui-epub-reopen-as-archive ()
  "Reopen the EPUB document using `archive-mode'."
  (interactive)
  (with-current-buffer (find-file-literally vui-epub-file-name)
    (archive-mode)))

(defun vui-epub-display-metadata ()
  "View the metadata of the EPUB document in a new buffer."
  (interactive)
  (let ((buffer "*EPUB metadata*")
        (metadata vui-epub-metadata)
        (version vui-epub-epub-version))
    (with-current-buffer (get-buffer-create buffer)
      (special-mode)
      (let (buffer-read-only)
        (erase-buffer)
        (insert (format "EPUB Version: %s\n" version))
        (dolist (item metadata)
          (seq-let (key &rest value) item
            (insert (format "%s: " (capitalize (symbol-name key))))
            (if value
                (if (eq key 'description)
                    (let ((beg (point)))
                      (insert value)
                      (shr-render-region beg (point)))
                  (insert (format "%s" value)))
              (insert (propertize "None" 'face 'italic)))
            (insert "\n")))
        (goto-char (point-min))))
    (pop-to-buffer buffer)))

(defun vui-epub-next-document (&optional count)
  "Go to the next document and render it.
Takes an optional COUNT, goes backward if COUNT is negative."
  (interactive "p")
  (vui-epub-goto-document (min (1- (length vui-epub-documents))
                           (+ vui-epub-documents-index (or count 1)))))

(defun vui-epub-previous-document (&optional count)
  "Go to the previous document and render it.
Takes an optional COUNT, goes forward if COUNT is negative."
  (interactive "p")
  (vui-epub-goto-document (max 0 (- vui-epub-documents-index (or count 1)))))

(defun vui-epub-scroll-up (arg)
  "Scroll with `scroll-up' or visit next chapter if at bottom."
  (interactive "P")
  (if (>= (window-end) (point-max))
      (vui-epub-next-document)
    (scroll-up arg)))

(defun vui-epub-scroll-down (arg)
  "Scroll with `scroll-down' or visit previous chapter if at top."
  (interactive "P")
  (if (and (<= (window-start) (point-min))
           (> vui-epub-documents-index 0))
      (progn
        (vui-epub-previous-document)
        (goto-char (point-max)))
    (scroll-down arg)))

(defun vui-epub--link-directories ()
  "Return directories used to resolve relative EPUB links."
  (let ((current-path (cdr (aref vui-epub-documents vui-epub-documents-index))))
    (delete-dups
     (delq nil
           (list (file-name-directory current-path)
                 (and vui-epub-content-file
                      (file-name-directory vui-epub-content-file)))))))

(defun vui-epub--document-index (filename)
  "Return the index of the document named by FILENAME, or nil.
FILENAME is resolved relative to the current document first, then
relative to the EPUB content root.  The latter covers EPUBs whose
links are written relative to the root rather than to the
containing document."
  (let ((paths (mapcar (lambda (dir)
                         (file-truename (expand-file-name filename dir)))
                       (vui-epub--link-directories))))
    (vui-epub-find-document
     (lambda (doc)
       (member (file-truename (cdr doc)) paths)))))

(defun vui-epub--resolve-file (filename)
  "Return the first existing file named FILENAME in the EPUB, or nil."
  (seq-find #'file-exists-p
            (mapcar (lambda (dir) (expand-file-name filename dir))
                    (vui-epub--link-directories))))

(defun vui-epub-visit-relative-file (filename target)
  "Visit the document as specified by FILENAME and TARGET.
FILENAME is resolved relative to the current document first, then
relative to the EPUB content root."
  (let (index)
    (when (not (zerop (length filename)))
      (let ((match (vui-epub--document-index filename)))
        (when (not match)
          (error "Couldn't locate document: %s" filename))
        (setq index match)))
    ;; HACK: this binding is only need for Emacs 27.1 and older, as of
    ;; Emacs 28.1, shr.el always adds the shr-target-id property
    (let ((shr-target-id target))
      (vui-epub-goto-document (or index vui-epub-documents-index))))
  (when target
    (let ((pos (point-min))
          done)
      (while (and (not done) pos)
        (let ((property (get-text-property pos 'shr-target-id)))
          (if (or (equal property target)
                  ;; NOTE: as of Emacs 28.1 this may be a list of targets
                  (and (consp property) (member target property)))
              (progn
                (goto-char pos)
                (recenter (1- (max 1 scroll-margin)))
                (setq done t))
            ;; NOTE: to catch the case of cursor starting out at the
            ;; `shr-target-id' property, change pos *after* checking
            (setq pos (next-single-property-change pos 'shr-target-id)))))
      (when (not done)
        (error "Couldn't locate target")))))

;; adapted from `shr-browse-url'
(defun vui-epub--state-buffer ()
  "Return the buffer that owns the current EPUB's buffer-local state."
  (if (and vui-epub-source-buffer (buffer-live-p vui-epub-source-buffer))
      vui-epub-source-buffer
    (current-buffer)))

(defun vui-epub-browse-url (url)
  "Follow URL.
External URLs are opened with `browse-url'.  URLs pointing to an
EPUB document are visited with `vui-epub-visit-relative-file';
other files packaged in the EPUB (images, stylesheets, ...) are
opened with `find-file'."
  (when (not url)
    (user-error "No link under point"))
  (if (vui-epub-external-url-p url)
      (browse-url url)
    (let (file)
      (with-current-buffer (vui-epub--state-buffer)
        (seq-let (filename target) (vui-epub-url-filename-and-target url)
          (if (or (zerop (length filename))
                  (vui-epub--document-index filename))
              (vui-epub-visit-relative-file filename target)
            (setq file (vui-epub--resolve-file filename))
            (when (not file)
              (error "Couldn't locate document: %s" filename)))))
      ;; Open the file outside `with-current-buffer', which would
      ;; otherwise restore the EPUB buffer and undo `find-file'.
      (when file
        (find-file file)))))

(defun vui-epub-copy-url (&optional mouse-event)
  "Copy the URL of the link at point to the kill ring.
MOUSE-EVENT, when it is a mouse event, moves point to the click
position first."
  (interactive (list last-nonmenu-event))
  (when (mouse-event-p mouse-event)
    (mouse-set-point mouse-event))
  (let ((url (get-text-property (point) 'shr-url)))
    (when (not url)
      (user-error "No link under point"))
    (kill-new url)
    (message "%s" url)))

(defun vui-epub-saved-places ()
  "Retrieve saved places in `vui-epub-save-place-file'."
  (when (and vui-epub-save-place-file (file-exists-p vui-epub-save-place-file))
    (with-temp-buffer
      (insert-file-contents-literally vui-epub-save-place-file)
      (goto-char (point-min))
      (condition-case nil
          (read (current-buffer))
        (error
         (vui-epub-warn "Failed to retrieve saved places from `vui-epub-save-place-file'")
         nil)))))

(defun vui-epub-saved-place (identifier)
  "Retrieve saved place for IDENTIFIER in `vui-epub-saved-place-file'."
  (cdr (assq identifier (vui-epub-saved-places))))

(defun vui-epub-save-place (identifier index point)
  "Save place as identified by IDENTIFIER, INDEX and POINT.
Saving is only done if `vui-epub-save-place-file' is set."
  (when vui-epub-save-place-file
    (let* ((place `(,identifier (index . ,index)
                                (point . ,point)))
           (places (cons place (assq-delete-all identifier (vui-epub-saved-places))))
           print-level
           print-length)
      (with-temp-file vui-epub-save-place-file
        (insert (prin1-to-string places))))))

(defun vui-epub--index-valid-p (documents index)
  (and (integerp index)
       (>= index 0)
       (< index (length documents))))

(defun vui-epub-history-back ()
  "Go back in the history to the last visited document."
  (interactive)
  (or vui-epub-history
      (user-error "This is the first document you looked at"))
  (let ((history-forward (cons (list vui-epub-documents-index (point))
                               vui-epub-history-forward)))
    (seq-let (index opoint) (car vui-epub-history)
      (setq vui-epub-history (cdr vui-epub-history))
      (vui-epub-goto-document index)
      (setq vui-epub-history (cdr vui-epub-history))
      (setq vui-epub-history-forward history-forward)
      (goto-char opoint)
      (recenter (1- (max 1 scroll-margin))))))

(defun vui-epub-history-forward ()
  "Go forward in the history of visited documents."
  (interactive)
  (or vui-epub-history-forward
      (user-error "This is the last document you looked at"))
  (let ((history-forward (cdr vui-epub-history-forward)))
    (seq-let (index opoint) (car vui-epub-history-forward)
      (vui-epub-goto-document index)
      (setq vui-epub-history-forward history-forward)
      (goto-char opoint)
      (recenter (1- (max 1 scroll-margin))))))

(defun vui-epub--initialize-temp-dir (path)
  (when (not path)
    (error "EPUB must be associated with file"))
  (when (not vui-epub-unzip-program)
    (error "unzip executable not found, customize `vui-epub-unzip-program'"))
  (setq vui-epub-work-dir (make-temp-file "vui-epub-" t ".epub"))
  (let ((exit-code (vui-epub-unzip-epub vui-epub-work-dir path)))
    (when (not (integerp exit-code))
      (vui-epub-clean-up)
      (error "EPUB extraction aborted by signal %s" exit-code))
    (when (> exit-code 1) ; exit code 1 is most likely a warning
      (vui-epub-clean-up)
      (error "EPUB extraction failed with exit code %d (see *vui-epub unzip* buffer)"
             exit-code)))
  (when (not (vui-epub-epub-valid-p vui-epub-work-dir))
    (vui-epub-clean-up)
    (error "Invalid EPUB file")))

(defun vui-epub-open-directory (dir)
  "Open EPUB buffer using DIR as directory of the document."
  (interactive "DEPUB directory to read: ")
  (let ((buf (generate-new-buffer (format "%s<vui-epub>" dir))))
    (with-current-buffer buf
      (setq vui-epub-initialize-work-dir-p nil)
      (setq vui-epub-remove-work-dir-on-exit-p nil)
      (setq vui-epub-work-dir dir)
      (vui-epub-mode))
    (switch-to-buffer buf)))

;;;###autoload
(define-derived-mode vui-epub-mode vui-mode "EPUB"
  "Major mode for reading EPUB documents.
Derived from `vui-mode' so that rendered content and EPUB state
live in the same buffer."
  (when vui-epub-remove-work-dir-on-exit-p
    (add-hook 'kill-buffer-hook 'vui-epub-clean-up nil t)
    (add-hook 'kill-emacs-hook 'vui-epub-clean-up-all)
    (add-hook 'change-major-mode-hook 'vui-epub-clean-up nil t))

  (when vui-epub-initialize-work-dir-p
    (vui-epub--initialize-temp-dir buffer-file-name))

  (let* ((content (vui-epub-slurp (vui-epub-container-filename vui-epub-work-dir) t))
         (content-file-name (vui-epub-container-content-filename content))
         (content-file (vui-epub-make-path vui-epub-work-dir content-file-name))
         (work-dir (file-name-directory content-file))
         (content (vui-epub-slurp content-file t)))
    (setq vui-epub-content-file content-file)
    (setq vui-epub-epub-version (vui-epub-content-version content))
    (setq vui-epub-metadata (vui-epub-content-metadata content))
    (setq vui-epub-documents (apply 'vector (vui-epub-content-files work-dir content)))
    (setq vui-epub-documents-index 0))
  (setq buffer-undo-list t)
  (setq vui-epub-file-name (buffer-file-name))
  ;; The buffer displays rendered HTML, not the archive's bytes, so
  ;; detach it from the EPUB file: saving the buffer must never
  ;; overwrite the EPUB.  `vui-epub-file-name' keeps the real path for
  ;; bookmarks, Org links, recentf and `vui-epub-reopen-as-archive'.
  (setq buffer-file-name nil)
  (setq buffer-file-truename nil)
  (setq buffer-file-number nil)
  (setq buffer-auto-save-file-name nil)
  ;; Re-renders mutate the buffer without going through
  ;; `vui-epub-render-document', so clear the modified flag whenever
  ;; the contents change instead of only after a full render.
  (add-hook 'after-change-functions #'vui-epub--keep-unmodified nil t)
  (add-hook 'kill-buffer-query-functions #'vui-epub--confirm-kill nil t)
  (set-buffer-modified-p nil)
  (setq-local bookmark-make-record-function
              'vui-epub-bookmark-make-record)
  (let ((place (vui-epub-saved-place (cdr (assq 'identifier vui-epub-metadata)))))
    (if place
        (let ((index (cdr (assq 'index place)))
              (point (cdr (assq 'point place))))
          (if (vui-epub--index-valid-p vui-epub-documents index)
              (progn
                (setq vui-epub-documents-index index)
                (vui-epub-render-document)
                (goto-char point))
            (vui-epub-warn "Couldn't restore last position")
            (vui-epub-render-document)))
      (vui-epub-render-document))))


;;; recentf interop

(defun vui-epub-add-to-recentf ()
  "Add real path to recentf list if possible."
  (when vui-epub-file-name
    (recentf-add-file vui-epub-file-name)))

(add-hook 'vui-epub-mode-hook 'vui-epub-add-to-recentf)
(add-hook 'vui-epub-mode-hook 'hack-dir-local-variables-non-file-buffer)


(defun vui-epub--find-file (file index point)
  "Open FILE in vui-epub-mode and go to the specified INDEX and POSITION.
If FILE is nil, the current buffer is used."
  (when file
    (find-file file))
  (unless (eq major-mode 'vui-epub-mode)
    (vui-epub-mode))
  (when (not (vui-epub--index-valid-p vui-epub-documents index))
    (error "Invalid documents index"))
  (setq vui-epub-documents-index index)
  (vui-epub-render-document)
  (goto-char point))

;; Bookmark interop
(defun vui-epub-bookmark-make-record  ()
  "Create a bookmark EPUB record."
  (cons (buffer-name)
        `((filename . ,vui-epub-file-name)
          (index . ,vui-epub-documents-index)
          (position . ,(point))
          (handler . vui-epub-bookmark-jump-handler))))

;;;###autoload
(defun vui-epub-bookmark-jump-handler (bmk)
  "The bookmark handler-function interface for bookmark BMK.

See also `vui-epub-bookmark-make-record'."
  (let ((file (bookmark-prop-get bmk 'filename))
        (index (bookmark-prop-get bmk 'index))
        (position (bookmark-prop-get bmk 'position)))
    (vui-epub--find-file file index position)))


;;; Org interop

;;;###autoload
(defun vui-epub-org-link-follow (path)
  "Follow vui-epub: link designated by PATH."
  (if (string-match "^\\(.*\\)::\\([0-9]+\\):\\([0-9]+\\)$" path)
      (let ((file (match-string 1 path))
            (index (string-to-number (match-string 2 path)))
            (point (string-to-number (match-string 3 path))))
        (vui-epub--find-file file index point))
    (error "Invalid vui-epub.el link")))

;;;###autoload
(defun vui-epub-org-link-store ()
  "Store current EPUB location as vui-epub: link."
  (when (and (eq major-mode 'vui-epub-mode) vui-epub-file-name)
    (when (not (integerp vui-epub-documents-index))
      (setq vui-epub-documents-index 0))
    (let ((org-store-props-function
           (if (fboundp 'org-link-store-props)
               'org-link-store-props
             'org-store-link-props))
          (link (format "vui-epub:%s::%d:%d"
                        vui-epub-file-name
                        vui-epub-documents-index
                        (point)))
          (description (or (alist-get 'title vui-epub-metadata)
                           (format "EPUB file at %s" vui-epub-file-name))))
      (funcall org-store-props-function
               :type "vui-epub"
               :link link
               :author (alist-get 'creator vui-epub-metadata)
               :language (alist-get 'language vui-epub-metadata)
               :initial (alist-get 'description vui-epub-metadata)
               :publisher (alist-get 'publisher vui-epub-metadata)
               :description description))))

;;;###autoload
(with-eval-after-load 'org
  (cond
   ((fboundp 'org-link-set-parameters)
    (org-link-set-parameters
     "vui-epub"
     :follow 'vui-epub-org-link-follow
     :store 'vui-epub-org-link-store))
   ((fboundp 'org-add-link-type)
    (org-add-link-type "vui-epub" 'vui-epub-org-link-follow)
    (add-hook 'org-store-link-functions 'vui-epub-org-link-store))))


;;; Imenu interop

(defun vui-epub-imenu-goto-function (_name filename target)
  "Visit imenu item using FILENAME and TARGET."
  ;; Make sure file is visited relative to toc file.
  (let ((vui-epub-documents-index 0))
    (vui-epub-visit-relative-file filename target)))

(defun vui-epub-imenu-create-index ()
  "Generate Imenu index."
  (let* ((toc-path (cdr (aref vui-epub-documents 0)))
         (ncxp (version< vui-epub-epub-version "3.0"))
         (toc (with-temp-buffer
                (if ncxp
                    (insert (vui-epub-ncx-to-html toc-path))
                  (insert-file-contents toc-path))
                (libxml-parse-html-region (point-min) (point-max)))))
    (mapcar
     (lambda (node)
       (let ((href (dom-attr node 'href))
             (label (dom-text node)))
         (seq-let (filename target) (vui-epub-url-filename-and-target href)
           (list label filename 'vui-epub-imenu-goto-function target))))
     (esxml-query-all "a" toc))))

(defun vui-epub-imenu-setup ()
  (setq imenu-create-index-function 'vui-epub-imenu-create-index))
(add-hook 'vui-epub-mode-hook 'vui-epub-imenu-setup)


;;; multi-isearch interop

(defun vui-epub-misearch-next-buffer (_buffer wrap)
  (if isearch-forward
      (cond
       ((< vui-epub-documents-index (1- (length vui-epub-documents)))
        (vui-epub-goto-document (1+ vui-epub-documents-index))
        (current-buffer))
       (wrap
        (vui-epub-goto-document 0)
        nil))
    (cond
     ((> vui-epub-documents-index 0)
      (vui-epub-goto-document (1- vui-epub-documents-index))
      (current-buffer))
     (wrap
      (vui-epub-goto-document (1- (length vui-epub-documents)))
      nil))))

(defun vui-epub-misearch-setup ()
  (setq-local multi-isearch-next-buffer-function #'vui-epub-misearch-next-buffer))
(add-hook 'vui-epub-mode-hook #'vui-epub-misearch-setup)

(provide 'vui-epub)
;;; vui-epub.el ends here
