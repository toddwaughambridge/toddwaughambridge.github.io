define(function(require) {

	var Op = require('nodes/op');
	var Atom = require('nodes/atom');
	var Instance = require('nodes/instance');
	var Link = require('link');
	var Flag = require('token').RewriteFlag();

	class RefOp extends Op {

		constructor(active) {
			super("ref", active);
		}

		copy() {
			return new RefOp(this.active);
		}

		rewrite(token) {
			var inLink = this.findLinksInto()[0];
			var outLink = this.findLinksOutOf()[0];

			var newNode = new Instance().addToGroup(this.group);
			var atomNode = new Atom().addToGroup(this.group);
			new Link(newNode.key,atomNode.key).addToGroup(this.group);

			inLink.changeTo(newNode.key);
			outLink.changeFrom(atomNode.key);

			this.delete();

			token.rewriteFlag = Flag.SEARCH;
			return inLink;
		}

	}

	return RefOp;
});
