# Spec: Who may do what to a document

A workspace has members. Each member holds one workspace role: guest, member, maintainer, or owner.

A document has an author (a user id), a visibility (private, workspace, or public), a locked flag, and a list of user ids granted explicit edit access.

The actions are: view, comment, edit, delete, share.

The rules, in the order they are decided:

1. The workspace **owner** may do anything, to any document.
2. A **per-document role override** may exist: the caller passes a table from user id to role, and if the acting user is in it, that role replaces their workspace role for this decision.
3. The document's **author** may always view, comment and edit their own document. They may delete it only if it is not locked. They may share it only if their effective role is member or above.
4. A **maintainer** may view, comment, edit and share any document that is not private (a private document belongs to its author alone). They may delete a document only if it is not locked.
5. A **member** may view and comment on any document whose visibility is workspace or public. They may edit one only if it is not locked **and** they are in the document's explicit edit list. They may never delete or share.
6. A **guest** may only view a public document. Nothing else.
7. Anything not allowed above is denied.

The answer must say **why** it was denied — "this document is private", "the document is locked", "a guest cannot comment" — and not merely false. A caller shows that reason to the user.

Ship at least: the effective-role lookup, the author check, the per-action decision, and one top-level "may this user do this to this document" entry point. Prove claims a business person would recognise — for example that a guest can never delete anything, that the owner is never denied, that a locked document is never deleted by whoever your rules exclude.
