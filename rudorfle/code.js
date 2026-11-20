var cookies = [
	{"description":"Morrisons Reindeer Gingerbread Biscuit","shop":"M","cost":1.0},
	{"description":"Morrisons Santa Hat Shortbread Biscuit","shop":"M","cost":1.0},
	{"description":"Morrisons Decorate Your Own Christmas Tree Gingerbread Biscuits Kit 4 Pack","shop":"M","cost":2.0},
	{"description":"Morrisons Decorate Your Own Gingerbread Christmas House Kit 668g","shop":"M","cost":6.0},
	{"description":"Morrisons Decorate Your Own Gingerbread Christmas Tree Kit 531g","shop":"M","cost":5.0},
	{"description":"Cadbury Mini Snowball Chocolate Cookies 4 Pack","shop":"M","cost":2.0},
	{"description":"Morrisons The Best Chocolate & Hazelnut Cookie","shop":"M","cost":1.0},
	{"description":"Morrisons Scarah Gingerbread Biscuit","shop":"M","cost":1.0},
	{"description":"Morrisons Ghoulian Gingerbread Biscuit","shop":"M","cost":1.0},
	{"description":"Cookies Party Platter 20 Pack","shop":"M","cost":4.5},
	{"description":"Morrisons The Best Triple Belgian Chocolate Cookies 4 Pack","shop":"M","cost":2.25},
	{"description":"Morrisons The Best Belgian Milk Chocolate Cookies 4 Pack","shop":"M","cost":2.25},
	{"description":"Market Street Gingerbread Man","shop":"M","cost":1.2},
	{"description":"Morrisons The Best Belgian White Chocolate Cookies 4 Pack","shop":"M","cost":2.25},
	{"description":"Morrisons The Best Salted Caramel Cookies 4 Pack","shop":"M","cost":2.25},
	{"description":"McGhees Baker Empire Biscuit 4 Pack","shop":"M","cost":1.85},
	{"description":"Morrisons The Best Raspberry & White Chocolate Cookie 65g","shop":"M","cost":2.25},
	{"description":"Giant 10\" Chocolate Cookie Happy Birthday","shop":"M","cost":7.0},
	{"description":"McGhee's Caramel Shortcake 4 Pack","shop":"M","cost":1.85},
	{"description":"Morrisons Single Chocolate Chunk Cookie","shop":"M","cost":0.5},
	{"description":"Irving's Homestyle Bakery Butter Shortbread 200g","shop":"M","cost":1.8},
	{"description":"Irving's Homestyle Bakery 6 Empire Biscuits 275g","shop":"M","cost":2.2},
	{"description":"Morrisons The Best All Butter Cherry Bakewell Cookies 200g","shop":"M","cost":2.5},
	{"description":"Irving's Homestyle Bakery Custard Creams 230g","shop":"M","cost":1.8},
	{"description":"Irving's Homestyle Bakery Gypsy Creams 230g","shop":"M","cost":1.8},
	{"description":"Oreo Original Cocoa Sandwich Cookies 154g","shop":"S","cost":1.5},
	{"description":"Sainsbury's Belgian Milk Chocolate Cookies Taste the Difference x4","shop":"S","cost":2.25},
	{"description":"Sainsbury's Milk Chocolate Cookies x5","shop":"S","cost":1.5},
	{"description":"Maryland Cookies Chocolate Chip 200g","shop":"S","cost":1.7},
	{"description":"Sainsbury's Stem Ginger Cookies Taste the Difference 200g","shop":"S","cost":2.95},
	{"description":"Fox's Triple Chocolate Cookies 180g","shop":"S","cost":2.5},
	{"description":"Sainsbury's Double Chocolate Cookies x5","shop":"S","cost":1.5},
	{"description":"Oreo Double Creme Sandwich Cookies 157g","shop":"S","cost":1.5},
	{"description":"Sainsbury's Dark Chocolate & Ginger Cookies Taste the Difference 200g","shop":"S","cost":2.95},
	{"description":"Sainsbury's Triple Belgian Chocolate Cookies Taste the Difference x4","shop":"S","cost":2.25},
	{"description":"Sainsbury's White Chocolate Cookies x5","shop":"S","cost":1.5},
	{"description":"Sainsbury's Oat & Sultana Cookies 200g","shop":"S","cost":1.45},
	{"description":"Sainsbury's Salted Caramel & Belgian Milk Chocolate Cookies x4","shop":"S","cost":2.25},
	{"description":"Sainsbury's Free From Chocolate Chip Cookies 150g","shop":"S","cost":1.7},
	{"description":"Sainsbury's Free From Ginger Crunch Cookies 150g","shop":"S","cost":1.7},
	{"description":"Maryland Cookies Chocolate Chip Twin Pack 400g","shop":"S","cost":2.5},
	{"description":"Sainsbury's Belgian Chocolate & Hazelnut Cookies 200g","shop":"S","cost":2.95},
	{"description":"Sainsbury's Free From Triple Chocolate Cookies 150g","shop":"S","cost":2.75},
	{"description":"LU Le Petit Chocolate Chip Cookies 184g","shop":"S","cost":2.25},
	{"description":"Oreo Gingerbread Flavour Sandwich Biscuits 154g","shop":"S","cost":1.5},
	{"description":"Sainsbury's Pistachio & Milk Chocolate Cookies 200g","shop":"S","cost":2.95},
	{"description":"Sainsbury's Oatmeal & Raisin Cookies x5","shop":"S","cost":1.5},
	{"description":"Maryland Cookies Double Chocolate 200g","shop":"S","cost":1.7},
	{"description":"Sainsbury's Quadruple Chocolate Cookies 200g","shop":"S","cost":2.95},
	{"description":"Maryland Mini Chocolate Chip Cookies Multipack x6","shop":"S","cost":1.55},
	{"description":"Fox's Chocolatey Cookies Assortment 365g","shop":"T","cost":4.5},
	{"description":"Oreo White Chocolate Covered Cookies 246g","shop":"T","cost":2.0},
	{"description":"Fox's Favourites Biscuit Selection 350g","shop":"T","cost":4.4},
	{"description":"Royal Dansk Danish Butter Cookies 340g","shop":"T","cost":4.0},
	{"description":"Tesco Finest Scottish Shortbread Assortment 400g","shop":"T","cost":5.8},
	{"description":"McVitie's Family Circle Biscuits 400g","shop":"T","cost":3.0},
	{"description":"Waitrose Flapjack All Butter Cookies 200g","shop":"W","cost":2.7},
	{"description":"Waitrose Stem Ginger All Butter Cookies 200g","shop":"W","cost":2.7},
	{"description":"Waitrose Belgian Double Chocolate All Butter Cookies 200g","shop":"W","cost":2.7},
	{"description":"Maryland Cookies Chocolate Chip 200g","shop":"W","cost":1.0},
	{"description":"Fox's Half Coated Milk Chocolate Cookies 157g","shop":"W","cost":3.0},
	{"description":"Fox's Milk Chocolate Cookies 180g","shop":"W","cost":3.0},
	{"description":"Waitrose Free From Gluten Stem Ginger Cookies 150g","shop":"W","cost":3.0},
	{"description":"Waitrose Belgian Triple Chocolate All Butter Cookies 200g","shop":"W","cost":2.7},
	{"description":"Waitrose Belgian White Chocolate All Butter Cookies 200g","shop":"W","cost":2.7},
	{"description":"Waitrose No.1 Free From Gluten Triple Choc Cookies 150g","shop":"W","cost":3.3},
	{"description":"Fox's Triple Chocolate Cookies 180g","shop":"W","cost":3.0},
	{"description":"Maryland Cookies Chocolate Chip Twin Pack 400g","shop":"W","cost":2.6},
	{"description":"Waitrose Dark Chocolate & Orange All Butter Cookies 200g","shop":"W","cost":2.7},
	{"description":"LU Le Petit Chocolate Chip Cookies 184g","shop":"W","cost":2.35},
	{"description":"Waitrose Free From Gluten Choc Chunk Cookies 150g","shop":"W","cost":3.0},
	{"description":"Waitrose Belgian Chocolate & Hazelnut All Butter Cookies 200g","shop":"W","cost":2.7},
	{"description":"Waitrose Triple Nut All Butter Cookies 200g","shop":"W","cost":2.7},
	{"description":"No.1 Italian Almond Ricciarelli Cookies 180g","shop":"W","cost":2.85},
	{"description":"Essential Bourbon Creams Biscuits 400g","shop":"W","cost":0.95},
	{"description":"Essential Custard Creams 150g","shop":"W","cost":0.35},
	{"description":"Essential Ginger Nuts 300g","shop":"W","cost":0.65},
	{"description":"Waitrose Shortbread Fingers 200g","shop":"W","cost":1.4},
	{"description":"Essential Milk Chocolate Digestive Biscuits 300g","shop":"W","cost":1.25},
	{"description":"McVitie's Digestives The Original Biscuits 315g","shop":"W","cost":1.75},
	{"description":"Jammie Dodgers Raspberry Flavour Biscuits 140g","shop":"W","cost":1.0},
	{"description":"Oreo Original Chocolate Sandwich Biscuits 154g","shop":"O","cost":1.0},
	{"description":"Oreo Double Stuff Chocolate Sandwich Biscuits 157g","shop":"O","cost":1.0},
	{"description":"Maryland Cookies Chocolate Chip 200g","shop":"O","cost":1.0},
	{"description":"Oreo Golden Sandwich Biscuits 154g","shop":"O","cost":1.0},
	{"description":"Oreo Gingerbread Sandwich Biscuits 154g","shop":"O","cost":1.0},
	{"description":"Maryland Cookies Double Chocolate 200g","shop":"O","cost":1.0},
	{"description":"Oreo Snowy Enrobed White Chocolate Coated Biscuits 246g","shop":"O","cost":2.0},
	{"description":"Maryland Cookies Chocolate Chip & Hazelnut 200g","shop":"O","cost":1.0},
	{"description":"Oreo Brownie Batter Sandwich Biscuits 154g","shop":"O","cost":1.0},
	{"description":"Maryland Cookies Chocolate Chip Minis Multipack 6 x 19.8g","shop":"O","cost":1.5},
	{"description":"Oreo Mini Chocolate Sandwich Biscuit Snack Packs 6 x 19g","shop":"O","cost":1.25},
	{"description":"M&S All Butter Double Chocolate Chunk Cookies 200g","shop":"O","cost":2.7},
	{"description":"M&S Pistachio & Almond Cookies 200g","shop":"O","cost":2.7},
	{"description":"M&S Chocolate Chip Cookies 200g","shop":"O","cost":1.2},
	{"description":"M&S All Butter Stem Ginger Cookies 200g","shop":"O","cost":2.7},
	{"description":"M&S Fruity Flapjack Cookies 200g","shop":"O","cost":2.7},
	{"description":"M&S Belgian Chocolate Chunk & Hazelnut Cookies 200g","shop":"O","cost":2.7},
	{"description":"M&S Sultana Cookies 200g","shop":"O","cost":2.7},
	{"description":"Oreo Original Vanilla Sandwich Cookies 6 x 22g","shop":"O","cost":1.25},
	{"description":"Fox's Half Coated Milk Chocolate Cookies 157g","shop":"O","cost":2.6},
	{"description":"M&S Sicilian Lemon & White Chocolate Cookies 200g","shop":"O","cost":2.7},
	{"description":"M&S Mini Chocolate Chip Cookie Bags 6 x 18g","shop":"O","cost":1.75},
	{"description":"M&S Made Without Belgian Chocolate Cookies 150g","shop":"O","cost":2.65},
	{"description":"McVitie's Family Circle Biscuit Selection 400g","shop":"O","cost":4.0},
	{"description":"Royal Dansk Danish Butter Cookies 340g","shop":"O","cost":4.0},
	{"description":"McVitie's Tasties Custard Cream Biscuits 300g","shop":"I","cost":1.0},
	{"description":"McVitie's Tasties Bourbon Cream Biscuits 300g","shop":"I","cost":1.0},
	{"description":"McVitie's Ginger Nuts Biscuits 250g","shop":"I","cost":1.6},
	{"description":"McVitie's Digestives The Original 2 x 315g","shop":"I","cost":2.95},
	{"description":"Paterson's Classic Shortbread Fingers Biscuits 300g","shop":"I","cost":1.0},
	{"description":"Fox's Golden Crunch Creams 200g","shop":"I","cost":1.0},
	{"description":"McVitie's Fruit Shortcake Biscuits 200g","shop":"I","cost":1.6},
	{"description":"Biscoff Biscuits Value Pack 250g","shop":"I","cost":1.0},
	{"description":"McVitie's Tasties Shorties Biscuits 300g","shop":"I","cost":1.0},
	{"description":"McVitie's Rich Tea Twin Pack 2 x 300g","shop":"I","cost":2.95},
	{"description":"Jammie Dodgers Raspberry Biscuits 2 x 105g","shop":"I","cost":1.2},
	{"description":"Fox's Viennese Milk Chocolate Melts 120g","shop":"I","cost":1.0},
	{"description":"McVitie's Tasties Original Digestive Biscuits 300g","shop":"I","cost":1.0},
	{"description":"Mrs Bector's Classic Biscuit Selection 400g","shop":"I","cost":1.0},
	{"description":"McVitie's Original Hobnobs Biscuits 255g","shop":"I","cost":1.6},
	{"description":"McVitie's Tasties Coconut Ring Biscuits 300g","shop":"I","cost":1.0},
	{"description":"McVitie's Tasties Nice Biscuits 250g","shop":"I","cost":1.0},
	{"description":"McVitie's Tasties Jam & Cream Sandwich Biscuits 150g","shop":"I","cost":1.0},
	{"description":"McVitie's Jammy's Raspberry Flavour Biscuits 136.5g","shop":"I","cost":0.6},
	{"description":"McVitie's Family Circle Biscuit Selection 400g","shop":"I","cost":3.0},
	{"description":"Fox's Classic Vanilla Cream Biscuits 5 x 25g","shop":"I","cost":1.0},
	{"description":"Fox's Milk Chocolate Cookies 180g","shop":"I","cost":1.5},
	{"description":"McVitie's Digestives Vanilla Creams Biscuits 168g","shop":"I","cost":1.0},
	{"description":"Fox's Ginger Crunch Creams 200g","shop":"I","cost":1.0},
	{"description":"Maryland Cookies Minis Chocolate Chip 6 Multipacks","shop":"I","cost":1.0}
]

function hash32(str) {
    let h = 2166136261;
    for (let i = 0; i < str.length; i++) {
        h ^= str.charCodeAt(i);
        h = Math.imul(h, 16777619);
    }
    return h >>> 0;
}

function mulberry32(a) {
    let t = a += 0x6D2B79F4;
    t = Math.imul(t ^ (t >>> 15), t | 1);
    t ^= t + Math.imul(t ^ (t >>> 7), t | 61);
    return (((t ^ (t >>> 14)) >>> 0) / 4294967296)
}

function rng(i) {
    const date = new Date()
    const year = date.getFullYear()
    const month = date.getMonth()
    const day = date.getDate()
    return Math.floor(mulberry32(hash32(`${year}-${month}-${day}-${i}`)) * cookies.length) 
}

function sleep(ms) {
    return new Promise(resolve => setTimeout(resolve, ms));
}

const options = document.querySelectorAll('.option');
document.querySelectorAll('.option').forEach((option, i) => {
    option.textContent = cookies[rng(i)].description;
});

document.querySelectorAll('[data-quantity-row]').forEach((row) => {
    row.addEventListener('click', (event) => {
        const button = event.target.closest('button[data-change]');
        if (!button) return;

        const output = row.querySelector('output');
        const quantityInput = row.querySelector('input[type="hidden"]');
        const quantity = Math.max(0, Number(quantityInput.value) + Number(button.dataset.change));
        output.value = quantity;
        quantityInput.value = quantity;
    });
});

function printy(message) {
    document.getElementById("score").innerHTML += message;
    window.scrollTo({
        top: document.body.scrollHeight,
        behavior: "smooth"
    });
}

async function revealScore(cost, score) {
    const startDate = new Date("2026-11-19");
    const today = new Date();
    const days = Math.floor((today - startDate) / (1000 * 60 * 60 * 24));
    printy("Rudorfle<br>");
    await sleep(1000);
    printy("Cookie Break #" + days)
    await sleep(1000);
    var remainingCost = cost;
    for (var i = 0; i < 100; i++) {
        if (i % 5 == 0) {
            printy("<br>")
        }
        if (remainingCost <= 0) {
            if (score == 0) {
                printy("❌")
            } else {
                printy("💷")
            }
            await sleep(30)
        } else {
            printy("🍪")
            remainingCost -= 10
            await sleep(50)
        }
    }
    printy("<br>")
    if (score == 0) {
        for (var i = 0; i < 5; i++) {
            printy("❌")
            await sleep(30)
        }
    } else {
        document.getElementsByName("quantity").forEach(async (quan, i) => {
        if (quan.value != 0) {
            printy("😍")
        } else {
           printy("🤷‍♀️")
        }
        await sleep(100)
    })
    }
    printy("<br>" + score)
    await sleep(2000)
    document.getElementById("copy-score").hidden = false;
}

document.getElementById("copy-score").addEventListener("click", async () => {
    const score = document.getElementById("score");
    const text = score.innerText;

    try {
        await navigator.clipboard.writeText(text);
        document.getElementById("copy-score").textContent = "✅ Copied!";
    } catch (err) {
        console.error("Clipboard failed:", err);
        document.getElementById("copy-score").textContent = "❌ Copy failed";
    }
});

document.addEventListener("submit", (event) => {
    event.preventDefault();
    var cost = 0;
    // var shops = [];
    var options = 0;
    var purchases = 0;
    document.getElementsByName("quantity").forEach((quan, i) => {
        cost += quan.value * Math.floor(cookies[rng(i)].cost * 100)
        if (quan.value != 0) {
            // if (!shops.includes(cookies[rng(i)].shop)) {
            //     shops.push(cookies[rng(i)].shop);
            // }
            options++;
        }
        purchases += quan.value * 1;
    })

	if (options > 0) {
		event.target.querySelector('button[type="submit"]').disabled = true;
		event.target.querySelectorAll('[data-quantity-row] button').forEach(button => {
			button.disabled = true;
		});
		
		var score = 0;
		if (cost <= 1000) {
			score = cost;
			// if (shops.length > 1) {
			//     score += (shops.length - 1) * 20;
			// }
			if (options > 1) {
				score += (options - 1) * 25;
			}
			score += purchases;
		}
		revealScore(cost, score);
	}
});