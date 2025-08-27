function rem<T(==)>(x: T, s: seq<T>): seq<T>
  decreases s
  ensures x !in rem(x, s)
  ensures forall i :: 0 <= i < |rem(x, s)| ==> rem(x, s)[i] in s
  ensures forall i :: 0 <= i < |s| && s[i] != x ==> s[i] in rem(x, s)
{}

class Address
{}

class Date
{}

class MessageId
{}

class Message
{
  var id: MessageId
  var content: string
  var date: Date
  var sender: Address
  var recipients: seq<Address>

  constructor (s: Address)
    ensures fresh(id)
    ensures fresh(date)
    ensures content == ""
    ensures sender == s
    ensures recipients == []
  {}

  method setContent(c: string)
    modifies this
    ensures content == c
  {}

  method setDate(d: Date)
    modifies this
    ensures date == d
  {}

  method addRecipient(p: nat, r: Address)
    modifies this
    requires p < |recipients|
    ensures |recipients| == |old(recipients)| + 1
    ensures recipients[p] == r
    ensures forall i :: 0 <= i < p ==> recipients[i] == old(recipients[i])
    ensures forall i :: p < i < |recipients| ==> recipients[i] == old(recipients[i-1])
  {}
}

class Mailbox {
  var messages: set<Message>
  var name: string

  constructor (n: string)
    ensures name == n
    ensures messages == {}
  {}

  method add(m: Message)
    modifies this
    ensures m in messages
    ensures messages == old(messages) + {m}
  {}

  method remove(m: Message)
    modifies this
    requires m in messages
    ensures m !in messages
    ensures messages == old(messages) - {m}
  {}

  method empty()
    modifies this
    ensures messages == {}
  {}
}

class MailApp {
  ghost var userboxes: set<Mailbox>

  var inbox: Mailbox
  var drafts: Mailbox
  var trash: Mailbox
  var sent: Mailbox

  var userboxList: seq<Mailbox>

  ghost predicate Valid()
    reads this
  {
    inbox != drafts &&
    inbox != trash &&
    inbox != sent &&
    drafts != trash &&
    drafts != sent &&

    inbox !in userboxList &&
    drafts !in userboxList &&
    trash !in userboxList &&
    sent !in userboxList &&

    forall i :: 0 <= i < |userboxList| ==> userboxList[i] in userboxes
  }

  constructor ()
  {}

  method deleteMailbox(mb: Mailbox)
    requires Valid()
    requires mb in userboxList
  {}

  method newMailbox(n: string)
    modifies this
    requires Valid()
    requires !exists mb | mb in userboxList :: mb.name == n
    ensures exists mb | mb in userboxList :: mb.name == n
  {}

  method newMessage(s: Address)
    modifies this.drafts
    requires Valid()
    ensures exists m | m in drafts.messages :: m.sender == s
  {}

  method moveMessage (m: Message, mb1: Mailbox, mb2: Mailbox)
    modifies mb1, mb2
    requires Valid()
    requires m in mb1.messages
    requires m !in mb2.messages
    ensures m !in mb1.messages
    ensures m in mb2.messages
  {}

  method deleteMessage (m: Message, mb: Mailbox)
    modifies m, mb, this.trash
    requires Valid()
    requires m in mb.messages
    requires m !in trash.messages
  {}

  method sendMessage(m: Message)
    modifies this.drafts, this.sent
    requires Valid()
    requires m in drafts.messages
    requires m !in sent.messages
  {}

  method emptyTrash()
    modifies this.trash
    requires Valid()
    ensures trash.messages == {}
  {}
}